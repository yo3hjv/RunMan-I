/*
 * MP3 Player for M5Stack TAB5
 * 
 * Features:
 * - Scans /mp3 folder on SD card
 * - Reads ID3 tags (title, artist, genre)
 * - Displays file list on screen
 * - Plays MP3, WAV, FLAC, AAC, OGG files
 * 
 * Supported formats by ESP8266Audio:
 * MP3, WAV, FLAC, AAC, OGG/Opus, MIDI, MOD, RTTTL
 */

#include <SPI.h>
#include <SD.h>
#include <vector>
#include <algorithm>
#include <math.h>

#include <AudioOutput.h>
#include <AudioFileSourceFS.h>
#include <AudioFileSourceID3.h>
#include <AudioGeneratorMP3.h>
#include <AudioGeneratorWAV.h>
#include <AudioGeneratorFLAC.h>
#include <AudioGeneratorAAC.h>

#include <M5Unified.h>
#include <M5GFX.h>

// TAB5 SD card SPI pins
#define SD_SPI_CS_PIN   42
#define SD_SPI_SCK_PIN  43
#define SD_SPI_MOSI_PIN 44
#define SD_SPI_MISO_PIN 39

// TAB5 Audio output mode
enum AudioOutputMode { OUTPUT_SPEAKER, OUTPUT_HEADPHONE };
static AudioOutputMode audioOutputMode = OUTPUT_SPEAKER;

// PI4IOE5V6408 I2C address for AMP control on TAB5
#define PI4IO_I2C_ADDR 0x43

// Audio channel
static constexpr uint8_t m5spk_virtual_channel = 0;

// Supported file extensions
const char* SUPPORTED_EXTENSIONS[] = {".mp3", ".wav", ".flac", ".aac", ".ogg"};
const int NUM_EXTENSIONS = 5;

// Track info structure
struct TrackInfo {
  String filename;      // Full path
  String displayName;   // Filename without path
  String title;         // From ID3 tag
  String artist;        // From ID3 tag
  String genre;         // From ID3 tag
  String fileType;      // Extension (MP3, WAV, etc.)
  uint32_t duration;    // Duration in seconds (if available)
  uint32_t fileSize;    // File size in bytes
};

// Global variables
std::vector<TrackInfo> trackList;
int currentTrackIndex = 0;
int displayStartIndex = 0;
int TRACKS_PER_PAGE = 15;  // Fixed at 15 tracks per page
int currentVolume = 128;  // 0-255
int currentPage = 0;
int totalPages = 1;
bool manualSpeakerMode = true;  // true = speaker, false = headphones only
bool isPaused = false;  // Pause state for PLAY/PAUSE button
bool volumeDragging = false;  // For smooth volume slider drag
bool trebleDragging = false;  // For treble slider drag
bool bassDragging = false;  // For bass slider drag
bool shuffleMode = false;  // Shuffle ON/OFF
int repeatMode = 0;  // 0=OFF, 1=REPEAT ONE, 2=REPEAT ALL
int currentTreble = 128;  // 0-255, 128 = neutral
int currentBass = 128;  // 0-255, 128 = neutral
bool screenOff = false;  // Screen off state (backlight only)
unsigned long lastBatteryUpdate = 0;  // For battery indicator refresh
unsigned long screenWakeTouchStart = 0;  // For 3-second hold to wake screen
bool loudnessMode = false;  // Loudness control ON/OFF

int trackListStartY_g = 0;
int trackLineHeight_g = 0;
uint32_t pausedFilePos = 0;  // Stores exact byte position in the audio file (for pause/resume)
// VU meter values (0-255 range, updated from audio samples)
int vuLeft = 0;
int vuRight = 0;
int vuPeakLeft = 0;
int vuPeakRight = 0;
unsigned long vuPeakTimeLeft = 0;
unsigned long vuPeakTimeRight = 0;
AudioOutputM5Speaker out;
AudioOutput *audioOut = &out;
// Touch debouncing for track selection
unsigned long lastTrackTouchTime = 0;
const unsigned long TRACK_TOUCH_DEBOUNCE = 300;  // ms

// Audio output class for M5Speaker
// Supports stereo (headphones) and mono (speaker - only L channel goes to amp)
class AudioOutputM5Speaker : public AudioOutput
{
  public:
    AudioOutputM5Speaker(m5::Speaker_Class* m5sound, uint8_t virtual_sound_channel = 0)
    {
      _m5sound = m5sound;
      _virtual_ch = virtual_sound_channel;
      _stereo_mode = false;  // Default to mono for speaker
    }
    virtual ~AudioOutputM5Speaker(void) {};
    virtual bool begin(void) override { return true; }
    
    // Set stereo mode (true for headphones, false for speaker)
    void setStereoMode(bool stereo) { _stereo_mode = stereo; }
    bool getStereoMode() { return _stereo_mode; }

    struct BiquadCoeffs {
      float b0 = 1.0f;
      float b1 = 0.0f;
      float b2 = 0.0f;
      float a1 = 0.0f;
      float a2 = 0.0f;
    };

    struct BiquadState {
      float z1 = 0.0f;
      float z2 = 0.0f;
      void reset() { z1 = 0.0f; z2 = 0.0f; }
    };

    static inline float biquadProcess(float x, const BiquadCoeffs& c, BiquadState& s)
    {
      float y = c.b0 * x + s.z1;
      s.z1 = c.b1 * x - c.a1 * y + s.z2;
      s.z2 = c.b2 * x - c.a2 * y;
      return y;
    }

    static inline void biquadSmoothTowards(BiquadCoeffs& cur, const BiquadCoeffs& tgt, float k)
    {
      cur.b0 += (tgt.b0 - cur.b0) * k;
      cur.b1 += (tgt.b1 - cur.b1) * k;
      cur.b2 += (tgt.b2 - cur.b2) * k;
      cur.a1 += (tgt.a1 - cur.a1) * k;
      cur.a2 += (tgt.a2 - cur.a2) * k;
    }

    static BiquadCoeffs designLowShelf(float fs, float f0, float dBgain, float S)
    {
      const float kPi = 3.14159265358979323846f;
      if (fs <= 1.0f) fs = 44100.0f;
      if (f0 < 5.0f) f0 = 5.0f;
      if (f0 > fs * 0.45f) f0 = fs * 0.45f;
      if (S <= 0.01f) S = 0.01f;

      float A = powf(10.0f, dBgain / 40.0f);
      float w0 = 2.0f * kPi * f0 / fs;
      float cw = cosf(w0);
      float sw = sinf(w0);
      float alpha = sw * 0.5f * sqrtf((A + 1.0f / A) * (1.0f / S - 1.0f) + 2.0f);
      float beta = 2.0f * sqrtf(A) * alpha;

      float b0 =    A * ((A + 1.0f) - (A - 1.0f) * cw + beta);
      float b1 =  2.0f * A * ((A - 1.0f) - (A + 1.0f) * cw);
      float b2 =    A * ((A + 1.0f) - (A - 1.0f) * cw - beta);
      float a0 =        (A + 1.0f) + (A - 1.0f) * cw + beta;
      float a1 =   -2.0f * ((A - 1.0f) + (A + 1.0f) * cw);
      float a2 =        (A + 1.0f) + (A - 1.0f) * cw - beta;

      BiquadCoeffs c;
      c.b0 = b0 / a0;
      c.b1 = b1 / a0;
      c.b2 = b2 / a0;
      c.a1 = a1 / a0;
      c.a2 = a2 / a0;
      return c;
    }

    static BiquadCoeffs designHighShelf(float fs, float f0, float dBgain, float S)
    {
      const float kPi = 3.14159265358979323846f;
      if (fs <= 1.0f) fs = 44100.0f;
      if (f0 < 5.0f) f0 = 5.0f;
      if (f0 > fs * 0.45f) f0 = fs * 0.45f;
      if (S <= 0.01f) S = 0.01f;

      float A = powf(10.0f, dBgain / 40.0f);
      float w0 = 2.0f * kPi * f0 / fs;
      float cw = cosf(w0);
      float sw = sinf(w0);
      float alpha = sw * 0.5f * sqrtf((A + 1.0f / A) * (1.0f / S - 1.0f) + 2.0f);
      float beta = 2.0f * sqrtf(A) * alpha;

      float b0 =    A * ((A + 1.0f) + (A - 1.0f) * cw + beta);
      float b1 = -2.0f * A * ((A - 1.0f) + (A + 1.0f) * cw);
      float b2 =    A * ((A + 1.0f) + (A - 1.0f) * cw - beta);
      float a0 =        (A + 1.0f) - (A - 1.0f) * cw + beta;
      float a1 =    2.0f * ((A - 1.0f) - (A + 1.0f) * cw);
      float a2 =        (A + 1.0f) - (A - 1.0f) * cw - beta;

      BiquadCoeffs c;
      c.b0 = b0 / a0;
      c.b1 = b1 / a0;
      c.b2 = b2 / a0;
      c.a1 = a1 / a0;
      c.a2 = a2 / a0;
      return c;
    }

    static BiquadCoeffs designPeakingEQ(float fs, float f0, float dBgain, float Q)
    {
      const float kPi = 3.14159265358979323846f;
      if (fs <= 1.0f) fs = 44100.0f;
      if (f0 < 5.0f) f0 = 5.0f;
      if (f0 > fs * 0.45f) f0 = fs * 0.45f;
      if (Q <= 0.05f) Q = 0.05f;

      float A = powf(10.0f, dBgain / 40.0f);
      float w0 = 2.0f * kPi * f0 / fs;
      float cw = cosf(w0);
      float sw = sinf(w0);
      float alpha = sw / (2.0f * Q);

      float b0 = 1.0f + alpha * A;
      float b1 = -2.0f * cw;
      float b2 = 1.0f - alpha * A;
      float a0 = 1.0f + alpha / A;
      float a1 = -2.0f * cw;
      float a2 = 1.0f - alpha / A;

      BiquadCoeffs c;
      c.b0 = b0 / a0;
      c.b1 = b1 / a0;
      c.b2 = b2 / a0;
      c.a1 = a1 / a0;
      c.a2 = a2 / a0;
      return c;
    }
    
    virtual bool ConsumeSample(int16_t sample[2]) override
    {
      float fs = (float)hertz;
      if (fs <= 1.0f) fs = 44100.0f;

      int bassDb = (currentBass - 128) * 12 / 128;
      int trebDb = (currentTreble - 128) * 12 / 128;
      float loudMidDb = loudnessMode ? -12.0f : 0.0f;

      uint32_t stateKey = ((uint32_t)(uint8_t)currentBass) | ((uint32_t)(uint8_t)currentTreble << 8) | ((uint32_t)(loudnessMode ? 1 : 0) << 16);
      if (stateKey != _dspLastKey || (int)fs != _dspLastFs) {
        _dspLastKey = stateKey;
        _dspLastFs = (int)fs;
        _bassTgt = designLowShelf(fs, 125.0f, (float)bassDb, 1.0f);
        _trebTgt = designHighShelf(fs, 10000.0f, (float)trebDb, 1.0f);
        _loudTgt = designPeakingEQ(fs, 1000.0f, loudMidDb, 0.7f);
      }

      biquadSmoothTowards(_bassCur, _bassTgt, 0.0015f);
      biquadSmoothTowards(_trebCur, _trebTgt, 0.0015f);
      biquadSmoothTowards(_loudCur, _loudTgt, 0.0015f);

      float xL = (float)sample[0];
      float xR = (float)sample[1];

      xL = biquadProcess(xL, _bassCur, _bassStateL);
      xR = biquadProcess(xR, _bassCur, _bassStateR);
      xL = biquadProcess(xL, _trebCur, _trebStateL);
      xR = biquadProcess(xR, _trebCur, _trebStateR);
      xL = biquadProcess(xL, _loudCur, _loudStateL);
      xR = biquadProcess(xR, _loudCur, _loudStateR);

      if (xL > 32767.0f) xL = 32767.0f; else if (xL < -32768.0f) xL = -32768.0f;
      if (xR > 32767.0f) xR = 32767.0f; else if (xR < -32768.0f) xR = -32768.0f;
      sample[0] = (int16_t)xL;
      sample[1] = (int16_t)xR;
      
      // Update VU meter values (simple peak detection)
      int absL = abs(sample[0]);
      int absR = abs(sample[1]);
      if (absL > _vuAccumL) _vuAccumL = absL;
      if (absR > _vuAccumR) _vuAccumR = absR;
      _vuSampleCount++;
      
      // Update global VU values every 256 samples
      if (_vuSampleCount >= 256) {
        vuLeft = _vuAccumL >> 7;  // Scale to 0-255
        vuRight = _vuAccumR >> 7;
        if (vuLeft > 255) vuLeft = 255;
        if (vuRight > 255) vuRight = 255;
        _vuAccumL = 0;
        _vuAccumR = 0;
        _vuSampleCount = 0;
      }
      
      if (_stereo_mode) {
        // Stereo mode for headphones: store L and R interleaved
        if (_tri_buffer_index < tri_buf_size)
        {
          _tri_buffer[_tri_index][_tri_buffer_index  ] = sample[0];  // L
          _tri_buffer[_tri_index][_tri_buffer_index+1] = sample[1];  // R
          _tri_buffer_index += 2;
          return true;
        }
      } else {
        // Mono mode for speaker: only L channel (amp receives HPOUT_L)
        if (_tri_buffer_index < tri_buf_size)
        {
          _tri_buffer[_tri_index][_tri_buffer_index] = sample[0];  // Only L
          _tri_buffer_index += 1;
          return true;
        }
      }
      flush();
      return false;
    }
    
    virtual void flush(void) override
    {
      if (_tri_buffer_index)
      {
        // playRaw: data, len, sampleRate, stereo, repeat, channel
        // stereo mode: L,R interleaved, len = total int16_t count
        // mono mode: single channel, len = sample count
        _m5sound->playRaw(_tri_buffer[_tri_index], _tri_buffer_index, hertz, _stereo_mode, 1, _virtual_ch);
        _tri_index = _tri_index < 2 ? _tri_index + 1 : 0;
        _tri_buffer_index = 0;
      }
    }
    
    virtual bool stop(void) override
    {
      flush();
      _m5sound->stop(_virtual_ch);
      return true;
    }

  protected:
    m5::Speaker_Class* _m5sound;
    uint8_t _virtual_ch;
    bool _stereo_mode;
    static constexpr size_t tri_buf_size = 1536;
    int16_t _tri_buffer[3][tri_buf_size];
    size_t _tri_buffer_index = 0;
    size_t _tri_index = 0;
    // VU meter accumulators
    int _vuAccumL = 0;
    int _vuAccumR = 0;
    int _vuSampleCount = 0;

    uint32_t _dspLastKey = 0;
    int _dspLastFs = 0;
    BiquadCoeffs _bassCur;
    BiquadCoeffs _bassTgt;
    BiquadCoeffs _trebCur;
    BiquadCoeffs _trebTgt;
    BiquadCoeffs _loudCur;
    BiquadCoeffs _loudTgt;
    BiquadState _bassStateL;
    BiquadState _bassStateR;
    BiquadState _trebStateL;
    BiquadState _trebStateR;
    BiquadState _loudStateL;
    BiquadState _loudStateR;
};

// Audio objects
static AudioOutputM5Speaker out(&M5.Speaker, m5spk_virtual_channel);
static AudioFileSourceFS* file = nullptr;
static AudioFileSourceID3* id3 = nullptr;
static AudioGeneratorMP3 mp3;
static AudioGeneratorWAV wav;
static AudioGeneratorFLAC flac;

// Current playing format
enum AudioFormat { FMT_NONE, FMT_MP3, FMT_WAV, FMT_FLAC, FMT_AAC, FMT_OGG };
static AudioFormat currentFormat = FMT_NONE;

// Temporary storage for ID3 callback
static String tempTitle = "";
static String tempArtist = "";
static String tempGenre = "";

// ID3 metadata callback
void ID3Callback(void *cbData, const char *type, bool isUnicode, const char *string)
{
  (void)cbData;
  if (string[0] == 0) return;
  
  if (strcmp(type, "Title") == 0 || strcmp(type, "TIT2") == 0) {
    tempTitle = String(string);
  } else if (strcmp(type, "Artist") == 0 || strcmp(type, "TPE1") == 0) {
    tempArtist = String(string);
  } else if (strcmp(type, "Genre") == 0 || strcmp(type, "TCON") == 0) {
    tempGenre = String(string);
  }
}

// Check if file has supported extension
bool isSupportedFile(const char* filename) {
  String fname = String(filename);
  fname.toLowerCase();
  for (int i = 0; i < NUM_EXTENSIONS; i++) {
    if (fname.endsWith(SUPPORTED_EXTENSIONS[i])) {
      return true;
    }
  }
  return false;
}

// Get file extension as uppercase string
String getFileType(const char* filename) {
  String fname = String(filename);
  int dotIndex = fname.lastIndexOf('.');
  if (dotIndex >= 0) {
    String ext = fname.substring(dotIndex + 1);
    ext.toUpperCase();
    return ext;
  }
  return "???";
}

// Get audio format from extension
AudioFormat getAudioFormat(const char* filename) {
  String fname = String(filename);
  fname.toLowerCase();
  if (fname.endsWith(".mp3")) return FMT_MP3;
  if (fname.endsWith(".wav")) return FMT_WAV;
  if (fname.endsWith(".flac")) return FMT_FLAC;
  if (fname.endsWith(".aac")) return FMT_AAC;
  if (fname.endsWith(".ogg")) return FMT_OGG;
  return FMT_NONE;
}

// Read ID3 tags from a file (quick scan)
void readID3Tags(TrackInfo& track) {
  tempTitle = "";
  tempArtist = "";
  tempGenre = "";
  
  AudioFileSourceFS tempFile(SD, track.filename.c_str());
  if (tempFile.isOpen()) {
    AudioFileSourceID3 tempId3(&tempFile);
    tempId3.RegisterMetadataCB(ID3Callback, nullptr);
    tempId3.open(track.filename.c_str());
    // Read a small amount to trigger ID3 parsing
    uint8_t buf[10];
    tempId3.read(buf, 10);
    tempId3.close();
  }
  
  track.title = tempTitle.length() > 0 ? tempTitle : "";
  track.artist = tempArtist.length() > 0 ? tempArtist : "";
  track.genre = tempGenre.length() > 0 ? tempGenre : "";
}

// Scan SD card for audio files
int scanSDCard(const char* folder) {
  trackList.clear();
  
  File root = SD.open(folder);
  if (!root) {
    M5.Display.println("Failed to open /mp3 folder!");
    return 0;
  }
  
  if (!root.isDirectory()) {
    M5.Display.println("/mp3 is not a directory!");
    root.close();
    return 0;
  }
  
  File file = root.openNextFile();
  while (file) {
    if (!file.isDirectory()) {
      const char* name = file.name();
      if (isSupportedFile(name)) {
        TrackInfo track;
        track.filename = String(folder) + "/" + String(name);
        track.displayName = String(name);
        track.fileType = getFileType(name);
        track.fileSize = file.size();
        track.duration = 0; // Will be calculated during playback
        
        trackList.push_back(track);
      }
    }
    file.close();
    file = root.openNextFile();
  }
  root.close();
  
  // Sort alphabetically by filename
  std::sort(trackList.begin(), trackList.end(), [](const TrackInfo& a, const TrackInfo& b) {
    return a.displayName < b.displayName;
  });
  
  // Read ID3 tags for each file - DISABLED for faster scanning
  // M5.Display.println("Reading ID3 tags...");
  // for (size_t i = 0; i < trackList.size(); i++) {
  //   readID3Tags(trackList[i]);
  //   // Show progress
  //   if (i % 10 == 0) {
  //     M5.Display.printf("  %d/%d\n", i, trackList.size());
  //   }
  // }
  
  return trackList.size();
}

// Format duration as mm:ss
String formatDuration(uint32_t seconds) {
  if (seconds == 0) return "--:--";
  int mins = seconds / 60;
  int secs = seconds % 60;
  char buf[8];
  snprintf(buf, sizeof(buf), "%02d:%02d", mins, secs);
  return String(buf);
}

// Check if headphones are inserted (PI4IOE5V6408 P7)
// Returns true if headphones are connected
bool isHeadphoneInserted() {
  // Read input register (0x0F) from PI4IOE5V6408
  // readRegister8 returns the value directly (0 on failure)
  uint8_t inputReg = M5.In_I2C.readRegister8(PI4IO_I2C_ADDR, 0x0F, 400000);
  // P7 is bit 7, LOW = headphone inserted
  return !(inputReg & 0x80);
}

// Set speaker amplifier state
// enabled = true: AMP on (speaker active)
// enabled = false: AMP off (headphones only)
// Note: M5Unified controls SPK_EN via PI4IOE5V6408 P1 automatically
// We need to control the Speaker class enable/disable instead
void setSpeakerAmp(bool enabled) {
  if (enabled) {
    // Re-enable speaker output
    M5.Speaker.setVolume(currentVolume);
    Serial.println("Speaker: ENABLED");
  } else {
    // Mute speaker but keep audio playing (for headphones)
    // Note: This doesn't actually mute - M5Unified doesn't support separate HP/SPK control
    // The hardware routes audio to both outputs simultaneously
    Serial.println("Speaker: Headphones connected (speaker still active)");
  }
}

// Update audio output based on headphone detection
void updateAudioOutput() {
  static bool lastHeadphoneState = false;
  static unsigned long lastCheck = 0;
  
  // Only check every 500ms to avoid excessive I2C traffic
  if (millis() - lastCheck < 500) return;
  lastCheck = millis();
  
  bool headphoneInserted = isHeadphoneInserted();
  
  if (headphoneInserted != lastHeadphoneState) {
    lastHeadphoneState = headphoneInserted;
    
    if (headphoneInserted) {
      audioOutputMode = OUTPUT_HEADPHONE;
      Serial.println("Headphones detected");
    } else {
      audioOutputMode = OUTPUT_SPEAKER;
      Serial.println("Headphones removed");
    }
    
    // Update UI to show current output mode
    drawVolumeSlider();
  }
}

// Toggle speaker/headphone mode manually
void toggleAudioOutput() {
  manualSpeakerMode = !manualSpeakerMode;
  
  if (manualSpeakerMode) {
    // Speaker mode: mono (only L channel), enable AMP
    out.setStereoMode(false);
    M5.In_I2C.bitOn(PI4IO_I2C_ADDR, 0x05, 0x02, 400000);
    audioOutputMode = OUTPUT_SPEAKER;
    Serial.println("Speaker: MONO (L channel only)");
  } else {
    // Headphone mode: stereo, disable speaker AMP
    out.setStereoMode(true);
    M5.In_I2C.bitOff(PI4IO_I2C_ADDR, 0x05, 0x02, 400000);
    audioOutputMode = OUTPUT_HEADPHONE;
    Serial.println("Headphones: STEREO");
  }
  
  drawFooter();
}

// Draw footer with volume, treble, bass, control buttons, pagination
void drawFooter() {
  int footerY = M5.Display.height() - 300;  // Even larger footer
  int screenW = M5.Display.width();
  
  // Clear footer area
  M5.Display.fillRect(0, footerY, screenW, 300, TFT_BLACK);
  
  // Separator line
  M5.Display.drawFastHLine(0, footerY, screenW, TFT_DARKGREY);
  
  // Row 0: Current track name (above volume slider)
  M5.Display.setFont(&fonts::Font4);
  M5.Display.setTextColor(TFT_YELLOW, TFT_BLACK);
  M5.Display.setCursor(10, footerY + 5);
  if (currentTrackIndex >= 0 && currentTrackIndex < trackList.size()) {
    String trackName = trackList[currentTrackIndex].displayName;
    if (trackName.length() > 50) {
      trackName = trackName.substring(0, 47) + "...";
    }
    M5.Display.printf("Now: %s", trackName.c_str());
  } else {
    M5.Display.print("No track selected");
  }
  
  // Slider dimensions - THICKER sliders with MORE space
  int sliderX = 55;
  int sliderWidth = screenW - 130;
  int sliderHeight = 40;  // THICKER sliders
  int sliderSpacing = 50;  // DOUBLE spacing between sliders
  
  // Row 1: Volume slider
  int volY = footerY + 35;
  M5.Display.setFont(&fonts::Font4);  // BIGGER font for labels
  M5.Display.setTextColor(TFT_WHITE, TFT_BLACK);
  M5.Display.setCursor(5, volY + 10);
  M5.Display.print("VOL");
  
  // Slider background
  M5.Display.fillRoundRect(sliderX, volY, sliderWidth, sliderHeight, 12, TFT_DARKGREY);
  
  // Slider fill
  int fillWidth = (sliderWidth - 8) * currentVolume / 255;
  if (fillWidth > 0) {
    M5.Display.fillRoundRect(sliderX + 4, volY + 4, fillWidth, sliderHeight - 8, 10, TFT_GREEN);
  }
  
  // Slider knob
  int knobX = sliderX + 4 + fillWidth - 12;
  if (knobX < sliderX + 4) knobX = sliderX + 4;
  M5.Display.fillRoundRect(knobX, volY + 3, 24, sliderHeight - 6, 8, TFT_WHITE);
  
  // Volume percentage
  M5.Display.setCursor(sliderX + sliderWidth + 8, volY + 10);
  M5.Display.printf("%3d%%", currentVolume * 100 / 255);
  
  // Row 2: Treble slider
  int trebY = volY + sliderSpacing;
  M5.Display.setTextColor(TFT_CYAN, TFT_BLACK);
  M5.Display.setCursor(5, trebY + 10);
  M5.Display.print("TRB");
  
  M5.Display.fillRoundRect(sliderX, trebY, sliderWidth, sliderHeight, 12, TFT_DARKGREY);
  int trebFill = (sliderWidth - 8) * currentTreble / 255;
  if (trebFill > 0) {
    M5.Display.fillRoundRect(sliderX + 4, trebY + 4, trebFill, sliderHeight - 8, 10, TFT_CYAN);
  }
  int trebKnob = sliderX + 4 + trebFill - 12;
  if (trebKnob < sliderX + 4) trebKnob = sliderX + 4;
  M5.Display.fillRoundRect(trebKnob, trebY + 3, 24, sliderHeight - 6, 8, TFT_WHITE);
  
  // Treble value (-12 to +12)
  int trebDb = (currentTreble - 128) * 12 / 128;
  M5.Display.fillRect(sliderX + sliderWidth + 5, trebY, 70, sliderHeight, TFT_BLACK);  // Clear text area
  M5.Display.setTextColor(TFT_CYAN, TFT_BLACK);
  M5.Display.setCursor(sliderX + sliderWidth + 8, trebY + 10);
  M5.Display.printf("%+d", trebDb);
  
  // Row 3: Bass slider
  int bassY = trebY + sliderSpacing;
  M5.Display.setTextColor(TFT_ORANGE, TFT_BLACK);
  M5.Display.setCursor(5, bassY + 10);
  M5.Display.print("BAS");
  
  M5.Display.fillRoundRect(sliderX, bassY, sliderWidth, sliderHeight, 12, TFT_DARKGREY);
  int bassFill = (sliderWidth - 8) * currentBass / 255;
  if (bassFill > 0) {
    M5.Display.fillRoundRect(sliderX + 4, bassY + 4, bassFill, sliderHeight - 8, 10, TFT_ORANGE);
  }
  int bassKnob = sliderX + 4 + bassFill - 12;
  if (bassKnob < sliderX + 4) bassKnob = sliderX + 4;
  M5.Display.fillRoundRect(bassKnob, bassY + 3, 24, sliderHeight - 6, 8, TFT_WHITE);
  
  // Bass value (-12 to +12)
  int bassDb = (currentBass - 128) * 12 / 128;
  M5.Display.fillRect(sliderX + sliderWidth + 5, bassY, 70, sliderHeight, TFT_BLACK);  // Clear text area
  M5.Display.setTextColor(TFT_ORANGE, TFT_BLACK);
  M5.Display.setCursor(sliderX + sliderWidth + 8, bassY + 10);
  M5.Display.printf("%+d", bassDb);
  
  // Row 4: Control buttons (EVEN BIGGER)
  int btnY = bassY + sliderSpacing + 5;
  int btnH = 55;  // BIGGER buttons
  int btnW = 90;  // BIGGER buttons
  int btnSpacing = 8;
  int startX = 5;
  
  M5.Display.setFont(&fonts::Font4);  // Larger font for buttons
  
  // STOP button
  M5.Display.fillRoundRect(startX, btnY, btnW, btnH, 8, TFT_RED);
  M5.Display.setTextColor(TFT_WHITE, TFT_RED);
  M5.Display.setCursor(startX + 16, btnY + 16);
  M5.Display.print("STOP");
  
  // PREV button
  int prevX = startX + btnW + btnSpacing;
  M5.Display.fillRoundRect(prevX, btnY, btnW, btnH, 8, TFT_BLUE);
  M5.Display.setTextColor(TFT_WHITE, TFT_BLUE);
  M5.Display.setCursor(prevX + 12, btnY + 16);
  M5.Display.print("PREV");
  
  // PLAY/PAUSE button (wider)
  int playX = prevX + btnW + btnSpacing;
  int playW = 110;
  if (isPlaying() && !isPaused) {
    M5.Display.fillRoundRect(playX, btnY, playW, btnH, 8, TFT_ORANGE);
    M5.Display.setTextColor(TFT_BLACK, TFT_ORANGE);
    M5.Display.setCursor(playX + 12, btnY + 16);
    M5.Display.print("PAUSE");
  } else {
    M5.Display.fillRoundRect(playX, btnY, playW, btnH, 8, TFT_GREEN);
    M5.Display.setTextColor(TFT_BLACK, TFT_GREEN);
    M5.Display.setCursor(playX + 22, btnY + 16);
    M5.Display.print("PLAY");
  }
  
  // NEXT button
  int nextX = playX + playW + btnSpacing;
  M5.Display.fillRoundRect(nextX, btnY, btnW, btnH, 8, TFT_BLUE);
  M5.Display.setTextColor(TFT_WHITE, TFT_BLUE);
  M5.Display.setCursor(nextX + 12, btnY + 16);
  M5.Display.print("NEXT");
  
  // SHUFFLE button (SHF)
  int shufX = nextX + btnW + btnSpacing;
  int smallBtnW = 70;
  if (shuffleMode) {
    M5.Display.fillRoundRect(shufX, btnY, smallBtnW, btnH, 8, TFT_MAGENTA);
    M5.Display.setTextColor(TFT_WHITE, TFT_MAGENTA);
  } else {
    M5.Display.fillRoundRect(shufX, btnY, smallBtnW, btnH, 8, TFT_DARKGREY);
    M5.Display.setTextColor(TFT_LIGHTGREY, TFT_DARKGREY);
  }
  M5.Display.setCursor(shufX + 10, btnY + 16);
  M5.Display.print("SHF");
  
  // REPEAT button (RPT)
  int rptX = shufX + smallBtnW + btnSpacing;
  uint16_t rptColor = (repeatMode > 0) ? TFT_CYAN : TFT_DARKGREY;
  uint16_t rptTextColor = (repeatMode > 0) ? TFT_BLACK : TFT_LIGHTGREY;
  M5.Display.fillRoundRect(rptX, btnY, smallBtnW, btnH, 8, rptColor);
  M5.Display.setTextColor(rptTextColor, rptColor);
  M5.Display.setCursor(rptX + 10, btnY + 16);
  if (repeatMode == 0) M5.Display.print("RPT");
  else if (repeatMode == 1) M5.Display.print("RP1");
  else M5.Display.print("RPA");
  
  // LOUDNESS button (between RPT and SPK/HP)
  int loudX = rptX + smallBtnW + btnSpacing;
  if (loudnessMode) {
    M5.Display.fillRoundRect(loudX, btnY, smallBtnW, btnH, 8, TFT_MAGENTA);
    M5.Display.setTextColor(TFT_WHITE, TFT_MAGENTA);
  } else {
    M5.Display.fillRoundRect(loudX, btnY, smallBtnW, btnH, 8, TFT_DARKGREY);
    M5.Display.setTextColor(TFT_LIGHTGREY, TFT_DARKGREY);
  }
  M5.Display.setCursor(loudX + 12, btnY + 16);
  M5.Display.print("\\_/");
  
  // SPK/HP toggle button
  int toggleX = screenW - 65;
  int toggleW = 60;
  if (manualSpeakerMode) {
    M5.Display.fillRoundRect(toggleX, btnY, toggleW, btnH, 8, TFT_ORANGE);
    M5.Display.setTextColor(TFT_BLACK, TFT_ORANGE);
    M5.Display.setCursor(toggleX + 8, btnY + 16);
    M5.Display.print("SPK");
  } else {
    M5.Display.fillRoundRect(toggleX, btnY, toggleW, btnH, 8, TFT_CYAN);
    M5.Display.setTextColor(TFT_BLACK, TFT_CYAN);
    M5.Display.setCursor(toggleX + 14, btnY + 16);
    M5.Display.print("HP");
  }
  
  // Row 5: Pagination (BIGGER buttons)
  totalPages = (trackList.size() + TRACKS_PER_PAGE - 1) / TRACKS_PER_PAGE;
  currentPage = displayStartIndex / TRACKS_PER_PAGE;
  
  int navY = btnY + btnH + 12;
  int navBtnW = 110;  // BIGGER nav buttons
  int navBtnH = 50;   // BIGGER nav buttons
  
  // Previous page button
  if (currentPage > 0) {
    M5.Display.fillRoundRect(10, navY, navBtnW, navBtnH, 8, TFT_BLUE);
    M5.Display.setTextColor(TFT_WHITE, TFT_BLUE);
    M5.Display.setFont(&fonts::Font4);
    M5.Display.setCursor(22, navY + 14);
    M5.Display.print("<PREV");
  }
  
  // Page indicator
  M5.Display.setTextColor(TFT_YELLOW, TFT_BLACK);
  M5.Display.setFont(&fonts::Font4);
  M5.Display.setCursor(screenW / 2 - 70, navY + 14);
  M5.Display.printf("Page %d / %d", currentPage + 1, totalPages);
  
  // Next page button
  if (currentPage < totalPages - 1) {
    M5.Display.fillRoundRect(screenW - navBtnW - 10, navY, navBtnW, navBtnH, 8, TFT_BLUE);
    M5.Display.setTextColor(TFT_WHITE, TFT_BLUE);
    M5.Display.setFont(&fonts::Font4);
    M5.Display.setCursor(screenW - navBtnW + 8, navY + 14);
    M5.Display.print("NEXT>");
  }
}

// Legacy function name for compatibility
void drawVolumeSlider() {
  drawFooter();
}

// Draw VU meters (call frequently from loop)
void drawVUMeters() {
  int screenW = M5.Display.width();
  int vuY = 45;  // Below header line
  int vuHeight = 18;
  int vuWidth = screenW - 50;
  int labelW = 25;
  int meterX = labelW + 5;
  
  // VU meter scale: 0-255 maps to -inf to +6dB
  // -9dB = ~90 (green), 0dB = ~180 (yellow), +6dB = 255 (red)
  int greenEnd = vuWidth * 90 / 255;   // -9dB
  int yellowEnd = vuWidth * 180 / 255; // 0dB
  
  // LEFT channel
  M5.Display.setFont(&fonts::Font2);
  M5.Display.setTextColor(TFT_WHITE, TFT_BLACK);
  M5.Display.setCursor(5, vuY + 2);
  M5.Display.print("L");
  
  // Clear and draw background
  M5.Display.fillRect(meterX, vuY, vuWidth + 20, vuHeight, TFT_BLACK);
  M5.Display.fillRect(meterX, vuY + 2, vuWidth, vuHeight - 4, TFT_DARKGREY);
  
  // Draw colored segments
  int leftWidth = vuWidth * vuLeft / 255;
  if (leftWidth > 0) {
    // Green segment (up to -9dB)
    int gw = min(leftWidth, greenEnd);
    if (gw > 0) M5.Display.fillRect(meterX, vuY + 2, gw, vuHeight - 4, TFT_GREEN);
    
    // Yellow segment (-9dB to 0dB)
    if (leftWidth > greenEnd) {
      int yw = min(leftWidth - greenEnd, yellowEnd - greenEnd);
      if (yw > 0) M5.Display.fillRect(meterX + greenEnd, vuY + 2, yw, vuHeight - 4, TFT_YELLOW);
    }
    
    // Red segment (0dB to +6dB)
    if (leftWidth > yellowEnd) {
      int rw = leftWidth - yellowEnd;
      if (rw > 0) M5.Display.fillRect(meterX + yellowEnd, vuY + 2, rw, vuHeight - 4, TFT_RED);
    }
  }
  
  // 0dB reference line (thin white vertical line)
  int zeroDbX = meterX + yellowEnd;
  M5.Display.drawFastVLine(zeroDbX, vuY + 2, vuHeight - 4, TFT_WHITE);
  
  // RIGHT channel
  int vuY2 = vuY + vuHeight + 2;
  M5.Display.setTextColor(TFT_WHITE, TFT_BLACK);
  M5.Display.setCursor(5, vuY2 + 2);
  M5.Display.print("R");
  
  // Clear and draw background
  M5.Display.fillRect(meterX, vuY2, vuWidth + 20, vuHeight, TFT_BLACK);
  M5.Display.fillRect(meterX, vuY2 + 2, vuWidth, vuHeight - 4, TFT_DARKGREY);
  
  // Draw colored segments
  int rightWidth = vuWidth * vuRight / 255;
  if (rightWidth > 0) {
    int gw = min(rightWidth, greenEnd);
    if (gw > 0) M5.Display.fillRect(meterX, vuY2 + 2, gw, vuHeight - 4, TFT_GREEN);
    
    if (rightWidth > greenEnd) {
      int yw = min(rightWidth - greenEnd, yellowEnd - greenEnd);
      if (yw > 0) M5.Display.fillRect(meterX + greenEnd, vuY2 + 2, yw, vuHeight - 4, TFT_YELLOW);
    }
    
    if (rightWidth > yellowEnd) {
      int rw = rightWidth - yellowEnd;
      if (rw > 0) M5.Display.fillRect(meterX + yellowEnd, vuY2 + 2, rw, vuHeight - 4, TFT_RED);
    }
  }
  
  // 0dB reference line for R channel
  M5.Display.drawFastVLine(zeroDbX, vuY2 + 2, vuHeight - 4, TFT_WHITE);
}

// Display track list on screen
void displayTrackList() {
  int screenW = M5.Display.width();
  int screenH = M5.Display.height();
  int footerH = 300;  // Larger footer for all controls
  int headerH = 45;   // Header with title
  int vuH = 45;       // VU meters area
  int vuGap = 100;    // Large gap between VU meters and track list
  int listStartY = headerH + vuH + vuGap;
  int lineHeight = 30;
  
  // Fixed 15 tracks per page
  // Available: 1280 - 300 (footer) - 190 (header+vu+gap) = 790px
  // 15 tracks x 30px = 450px - fits easily!
  TRACKS_PER_PAGE = 15;
  
  M5.Display.fillScreen(TFT_BLACK);
  M5.Display.setTextColor(TFT_WHITE, TFT_BLACK);
  M5.Display.setFont(&fonts::Font4);
  
  // Header with battery indicator and screen off button
  M5.Display.setCursor(10, 10);
  M5.Display.setTextColor(TFT_CYAN, TFT_BLACK);
  M5.Display.printf("Music RunMan - %d tracks", trackList.size());
  
  // Battery indicator (right side of header, before OFF button)
  int batLevel = M5.Power.getBatteryLevel();
  bool isCharging = M5.Power.isCharging();
  int batX = screenW - 180;  // Moved more to the left
  int batY = 8;
  
  // Battery icon outline
  M5.Display.drawRect(batX, batY, 40, 20, TFT_WHITE);
  M5.Display.fillRect(batX + 40, batY + 5, 4, 10, TFT_WHITE);  // Battery tip
  
  // Battery fill (color based on level)
  int fillW = 36 * batLevel / 100;
  uint16_t batColor = TFT_GREEN;
  if (batLevel <= 20) batColor = TFT_RED;
  else if (batLevel <= 50) batColor = TFT_YELLOW;
  if (fillW > 0) {
    M5.Display.fillRect(batX + 2, batY + 2, fillW, 16, batColor);
  }
  
  // Charging indicator or percentage
  M5.Display.setFont(&fonts::Font4);  // Bigger font for battery %
  M5.Display.setCursor(batX + 50, batY - 2);  // +2px more spacing
  if (isCharging) {
    M5.Display.setTextColor(TFT_RED, TFT_BLACK);
    M5.Display.printf("%d%%+", batLevel);
  } else {
    M5.Display.setTextColor(TFT_WHITE, TFT_BLACK);
    M5.Display.printf("%d%%", batLevel);
  }
  
  // Screen OFF button (far right)
  int btnOffX = screenW - 45;
  int btnOffY = 5;
  M5.Display.fillRoundRect(btnOffX, btnOffY, 40, 30, 5, TFT_DARKGREY);
  M5.Display.setTextColor(TFT_WHITE, TFT_DARKGREY);
  M5.Display.setFont(&fonts::Font2);
  M5.Display.setCursor(btnOffX + 6, btnOffY + 8);
  M5.Display.print("OFF");
  
  M5.Display.setFont(&fonts::Font4);
  M5.Display.drawFastHLine(0, 40, screenW, TFT_CYAN);
  
  // VU meters will be drawn in loop() for animation
  // Draw initial empty VU meters
  drawVUMeters();
  
  // Separator line right after VU meters (before the gap)
  int vuEndY = headerH + vuH;
  M5.Display.drawFastHLine(0, vuEndY, screenW, TFT_DARKGREY);
  
  // Track list - VERY BIG font for filenames
  M5.Display.setFont(&fonts::FreeMonoBold18pt7b);  // 18pt = much bigger!
  lineHeight = M5.Display.fontHeight() + 4;
  trackListStartY_g = listStartY;
  trackLineHeight_g = lineHeight;
  int y = listStartY;
  
  for (int i = displayStartIndex; i < trackList.size() && i < displayStartIndex + TRACKS_PER_PAGE; i++) {
    TrackInfo& track = trackList[i];
    
    // Highlight current track
    if (i == currentTrackIndex) {
      M5.Display.fillRect(0, y, screenW, lineHeight, TFT_DARKGREEN);
      M5.Display.setTextColor(TFT_WHITE, TFT_DARKGREEN);
    } else {
      M5.Display.setTextColor(TFT_WHITE, TFT_BLACK);
    }
    
    M5.Display.setCursor(5, y + 4);
    
    // Number and filename on single line, truncated
    String filename = track.displayName;
    int maxLen = 30;  // Max chars that fit
    if (filename.length() > maxLen) {
      filename = filename.substring(0, maxLen - 2) + "..";
    }
    M5.Display.printf("%2d.%s", i + 1, filename.c_str());
    
    y += lineHeight;
  }
  
  // Draw footer with controls
  drawFooter();
}

/* // Pause current playback - just mute, don't stop decoder
void pausePlayback() {
  if (!isPlaying()) return;
  isPaused = true;
  // Mute the speaker but keep decoder running
  M5.Speaker.setVolume(0);
  drawFooter();
}   */

// Pause - store pause position in global variable
void pausePlayback() {
  if (!isPlaying() || isPaused || file == nullptr) return;

  isPaused = true;

  // Save current file position
  pausedFilePos = file->getPos();

  // Stop decoder ONLY (do not close file)
  switch (currentFormat) {
    case FMT_MP3:
      if (mp3.isRunning()) mp3.stop();
      break;
    case FMT_WAV:
      if (wav.isRunning()) wav.stop();
      break;
    case FMT_FLAC:
      if (flac.isRunning()) flac.stop();
      break;
    default:
      break;
  }

  out.stop();   // stop I2S cleanly
  drawFooter();
}

/* // Resume playback - unmute and continue from where we paused
void resumePlayback() {
  if (isPaused) {
    isPaused = false;
    // Restore volume
    M5.Speaker.setVolume(currentVolume);
    drawFooter();
  }
}    */
// Resume playing from stored Pause byte
void resumePlayback() {
  if (!isPaused || file == nullptr) return;

  isPaused = false;

  // Repozitionare exacta in fisier
  file->seek(pausedFilePos, SEEK_SET);

  switch (currentFormat) {

    case FMT_MP3:
      if (id3) {
        mp3.begin((AudioFileSource*)id3, audioOut);
      } else {
        mp3.begin((AudioFileSource*)file, audioOut);
      }
      break;

    case FMT_WAV:
      wav.begin((AudioFileSource*)file, audioOut);
      break;

    case FMT_FLAC:
      flac.begin((AudioFileSource*)file, audioOut);
      break;

    default:
      break;
  }

  drawFooter();
}

// Toggle play/pause
void togglePlayPause() {
  if (isPlaying() && !isPaused) {
    pausePlayback();
  } else if (isPaused) {
    resumePlayback();
  } else if (currentTrackIndex >= 0) {
    // Start playing current track
    isPaused = false;
    playTrack(currentTrackIndex);
  } else if (trackList.size() > 0) {
    // Start playing first track
    isPaused = false;
    playTrack(0);
  }
}

// Play previous track
void playPrevious() {
  if (trackList.size() == 0) return;
  isPaused = false;
  int newIndex = currentTrackIndex - 1;
  if (newIndex < 0) newIndex = trackList.size() - 1;
  playTrack(newIndex);
}

// Play next track (respects SHUFFLE mode)
void playNext() {
  if (trackList.size() == 0) return;
  isPaused = false;
  
  int newIndex;
  if (shuffleMode) {
    // SHUFFLE: pick random track different from current
    newIndex = random(trackList.size());
    if (newIndex == currentTrackIndex && trackList.size() > 1) {
      newIndex = (newIndex + 1) % trackList.size();
    }
  } else {
    // Normal: next sequential track
    newIndex = currentTrackIndex + 1;
    if (newIndex >= trackList.size()) newIndex = 0;
  }
  playTrack(newIndex);
}

// Stop current playback completely
void stopPlayback() {
  switch (currentFormat) {
    case FMT_MP3:
      if (mp3.isRunning()) { mp3.stop(); }
      break;
    case FMT_WAV:
      if (wav.isRunning()) { wav.stop(); }
      break;
    case FMT_FLAC:
      if (flac.isRunning()) { flac.stop(); }
      break;
    default:
      break;
  }
  
  out.stop();
  
  if (id3) {
    id3->close();
    delete id3;
    id3 = nullptr;
  }
  if (file) {
    file->close();
    delete file;
    file = nullptr;
  }
  
  currentFormat = FMT_NONE;
  isPaused = false;
}

// Play a track by index
void playTrack(int index) {
  if (index < 0 || index >= trackList.size()) return;
  
  stopPlayback();
  
  currentTrackIndex = index;
  TrackInfo& track = trackList[index];
  
  M5.Display.setCursor(10, M5.Display.height() - 50);
  M5.Display.setTextColor(TFT_GREEN, TFT_BLACK);
  M5.Display.printf("Playing: %s", track.displayName.c_str());
  
  file = new AudioFileSourceFS(SD, track.filename.c_str());
  currentFormat = getAudioFormat(track.filename.c_str());
  
  switch (currentFormat) {
    case FMT_MP3:
      id3 = new AudioFileSourceID3(file);
      id3->RegisterMetadataCB(ID3Callback, nullptr);
      mp3.begin(id3, &out);
      break;
    case FMT_WAV:
      wav.begin(file, &out);
      break;
    case FMT_FLAC:
      flac.begin(file, &out);
      break;
    default:
      M5.Display.println("Unsupported format!");
      stopPlayback();
      return;
  }
  
  displayTrackList();
}

// Check if any audio is playing
bool isPlaying() {
  switch (currentFormat) {
    case FMT_MP3: return mp3.isRunning();
    case FMT_WAV: return wav.isRunning();
    case FMT_FLAC: return flac.isRunning();
    default: return false;
  }
}

// Audio loop - must be called frequently
void audioLoop() {
  bool running = false;
  
  switch (currentFormat) {
    case FMT_MP3:
      if (mp3.isRunning()) {
        running = mp3.loop();
      }
      break;
    case FMT_WAV:
      if (wav.isRunning()) {
        running = wav.loop();
      }
      break;
    case FMT_FLAC:
      if (flac.isRunning()) {
        running = flac.loop();
      }
      break;
    default:
      break;
  }
  
  // Auto-advance to next track when finished (only if not paused)
  if (currentFormat != FMT_NONE && !running && !isPaused) {
    // Handle repeat modes
    if (repeatMode == 1) {
      // REPEAT ONE - replay same track
      playTrack(currentTrackIndex);
    } else if (shuffleMode) {
      // SHUFFLE mode - pick random track
      int nextIndex = random(trackList.size());
      if (nextIndex == currentTrackIndex && trackList.size() > 1) {
        nextIndex = (nextIndex + 1) % trackList.size();
      }
      playTrack(nextIndex);
    } else if (currentTrackIndex + 1 < trackList.size()) {
      // Normal sequential playback
      playTrack(currentTrackIndex + 1);
    } else if (repeatMode == 2) {
      // REPEAT ALL - loop back to first track
      playTrack(0);
    } else {
      // End of playlist
      stopPlayback();
      displayTrackList();
    }
  }
}

// Initialize headphone detection at startup
void initHeadphoneDetection() {
  // Configure P7 as input for headphone detection
  // PI4IOE5V6408 registers:
  // 0x03 = Direction (0=output, 1=input)
  // 0x0F = Input state
  
  // Set P7 as input (bit 7 = 1) - don't touch P1, let M5Unified control it
  M5.In_I2C.bitOn(PI4IO_I2C_ADDR, 0x03, 0x80, 400000);
  
  // Check initial state
  bool hpInserted = isHeadphoneInserted();
  Serial.printf("Headphone detection at startup: %s\n", hpInserted ? "INSERTED" : "NOT INSERTED");
  
  audioOutputMode = hpInserted ? OUTPUT_HEADPHONE : OUTPUT_SPEAKER;
}

void setup() {
  // Initialize M5
  M5.begin();
  M5.Display.setRotation(0);  // Portrait mode for more tracks
  M5.Display.fillScreen(TFT_BLACK);
  
  // Splash screen with copyright
  int screenW = M5.Display.width();
  int screenH = M5.Display.height();
  M5.Display.setFont(&fonts::FreeMonoBold18pt7b);
  M5.Display.setTextColor(TFT_CYAN);
  M5.Display.setTextDatum(MC_DATUM);
  M5.Display.drawString("Music RunMan", screenW / 2, screenH / 2 - 40);
  M5.Display.setFont(&fonts::Font4);
  M5.Display.setTextColor(TFT_WHITE);
  M5.Display.drawString("for M5Stack TAB5", screenW / 2, screenH / 2 + 10);
  M5.Display.setTextColor(TFT_YELLOW);
  M5.Display.drawString("Copyright: Adrian Florescu @2026", screenW / 2, screenH / 2 + 50);
  M5.Display.setTextDatum(TL_DATUM);
  delay(2500);  // Show splash for 2.5 seconds
  
  M5.Display.fillScreen(TFT_BLACK);
  M5.Display.setFont(&fonts::Font4);
  M5.Display.setTextColor(TFT_WHITE);
  M5.Display.setCursor(10, 10);
  M5.Display.println("Music RunMan TAB5");
  M5.Display.println("Initializing...");
  
  // Initialize SD card
  SPI.begin(SD_SPI_SCK_PIN, SD_SPI_MISO_PIN, SD_SPI_MOSI_PIN, SD_SPI_CS_PIN);
  if (!SD.begin(SD_SPI_CS_PIN, SPI, 25000000)) {
    M5.Display.setTextColor(TFT_RED);
    M5.Display.println("SD card not detected!");
    while (1) { delay(1000); }
  }
  M5.Display.println("SD card OK!");
  
  // Initialize speaker - TAB5 uses ES8388 codec via I2S
  // IMPORTANT: stereo must be true in config for I2S to output stereo
  // AND playRaw must be called with stereo=true
  auto spk_cfg = M5.Speaker.config();
  spk_cfg.sample_rate = 48000;
  spk_cfg.stereo = true;   // Required for stereo I2S output
  spk_cfg.buzzer = false;
  M5.Speaker.config(spk_cfg);
  M5.Speaker.begin();
  M5.Speaker.setVolume(currentVolume);
  M5.Display.println("Speaker OK (Stereo)!");
  
  // Initialize headphone detection and set initial audio mode
  initHeadphoneDetection();
  // Set stereo mode based on initial state (speaker=mono, headphones=stereo)
  out.setStereoMode(!manualSpeakerMode);
  M5.Display.printf("Audio: %s\n", manualSpeakerMode ? "Speaker (MONO)" : "Headphones (STEREO)");
  
  // Scan for audio files
  M5.Display.println("Scanning /mp3 folder...");
  int count = scanSDCard("/mp3");
  M5.Display.printf("Found %d audio files\n", count);
  
  delay(1000);
  
  // Display track list
  if (count > 0) {
    displayTrackList();
  } else {
    M5.Display.setTextColor(TFT_YELLOW);
    M5.Display.println("\nNo audio files found in /mp3 folder!");
    M5.Display.println("Supported formats: MP3, WAV, FLAC, AAC, OGG");
  }
}

// Handle volume slider touch (with drag support)
void handleVolumeSlider(int touchX) {
  int footerY = M5.Display.height() - 300;
  int volY = footerY + 35;  // After track name row
  int sliderX = 55;
  int sliderWidth = M5.Display.width() - 130;
  int sliderHeight = 40;  // THICKER
  
  // Calculate new volume
  int newVolume = (touchX - sliderX) * 255 / sliderWidth;
  if (newVolume < 0) newVolume = 0;
  if (newVolume > 255) newVolume = 255;
  
  if (newVolume != currentVolume) {
    currentVolume = newVolume;
    M5.Speaker.setVolume(currentVolume);
    
    // Redraw only the volume slider area
    M5.Display.fillRect(sliderX, volY, sliderWidth + 70, sliderHeight + 2, TFT_BLACK);
    M5.Display.fillRoundRect(sliderX, volY, sliderWidth, sliderHeight, 12, TFT_DARKGREY);
    
    int fillWidth = (sliderWidth - 8) * currentVolume / 255;
    if (fillWidth > 0) {
      M5.Display.fillRoundRect(sliderX + 4, volY + 4, fillWidth, sliderHeight - 8, 10, TFT_GREEN);
    }
    
    int knobX = sliderX + 4 + fillWidth - 12;
    if (knobX < sliderX + 4) knobX = sliderX + 4;
    M5.Display.fillRoundRect(knobX, volY + 3, 24, sliderHeight - 6, 8, TFT_WHITE);
    
    M5.Display.setFont(&fonts::Font4);
    M5.Display.setTextColor(TFT_WHITE, TFT_BLACK);
    M5.Display.setCursor(sliderX + sliderWidth + 8, volY + 10);
    M5.Display.printf("%3d%%", currentVolume * 100 / 255);
  }
}

// Handle treble slider touch
void handleTrebleSlider(int touchX) {
  int footerY = M5.Display.height() - 300;
  int trebY = footerY + 35 + 50;  // volY + sliderSpacing
  int sliderX = 55;
  int sliderWidth = M5.Display.width() - 130;
  int sliderHeight = 40;  // THICKER
  
  int newTreble = (touchX - sliderX) * 255 / sliderWidth;
  if (newTreble < 0) newTreble = 0;
  if (newTreble > 255) newTreble = 255;
  
  if (newTreble != currentTreble) {
    currentTreble = newTreble;
    // TODO: Apply treble to audio processing
    
    M5.Display.fillRect(sliderX, trebY, sliderWidth + 70, sliderHeight + 2, TFT_BLACK);
    M5.Display.fillRoundRect(sliderX, trebY, sliderWidth, sliderHeight, 12, TFT_DARKGREY);
    
    int fillWidth = (sliderWidth - 8) * currentTreble / 255;
    if (fillWidth > 0) {
      M5.Display.fillRoundRect(sliderX + 4, trebY + 4, fillWidth, sliderHeight - 8, 10, TFT_CYAN);
    }
    
    int knobX = sliderX + 4 + fillWidth - 12;
    if (knobX < sliderX + 4) knobX = sliderX + 4;
    M5.Display.fillRoundRect(knobX, trebY + 3, 24, sliderHeight - 6, 8, TFT_WHITE);
    
    int trebDb = (currentTreble - 128) * 12 / 128;
    M5.Display.fillRect(sliderX + sliderWidth + 5, trebY, 70, sliderHeight, TFT_BLACK);  // Clear text area
    M5.Display.setFont(&fonts::Font4);
    M5.Display.setTextColor(TFT_CYAN, TFT_BLACK);
    M5.Display.setCursor(sliderX + sliderWidth + 8, trebY + 10);
    M5.Display.printf("%+d", trebDb);
  }
}

// Handle bass slider touch
void handleBassSlider(int touchX) {
  int footerY = M5.Display.height() - 300;
  int bassY = footerY + 35 + 100;  // volY + 2*sliderSpacing
  int sliderX = 55;
  int sliderWidth = M5.Display.width() - 130;
  int sliderHeight = 40;  // THICKER
  
  int newBass = (touchX - sliderX) * 255 / sliderWidth;
  if (newBass < 0) newBass = 0;
  if (newBass > 255) newBass = 255;
  
  if (newBass != currentBass) {
    currentBass = newBass;
    // TODO: Apply bass to audio processing
    
    M5.Display.fillRect(sliderX, bassY, sliderWidth + 70, sliderHeight + 2, TFT_BLACK);
    M5.Display.fillRoundRect(sliderX, bassY, sliderWidth, sliderHeight, 12, TFT_DARKGREY);
    
    int fillWidth = (sliderWidth - 8) * currentBass / 255;
    if (fillWidth > 0) {
      M5.Display.fillRoundRect(sliderX + 4, bassY + 4, fillWidth, sliderHeight - 8, 10, TFT_ORANGE);
    }
    
    int knobX = sliderX + 4 + fillWidth - 12;
    if (knobX < sliderX + 4) knobX = sliderX + 4;
    M5.Display.fillRoundRect(knobX, bassY + 3, 24, sliderHeight - 6, 8, TFT_WHITE);
    
    int bassDb = (currentBass - 128) * 12 / 128;
    M5.Display.fillRect(sliderX + sliderWidth + 5, bassY, 70, sliderHeight, TFT_BLACK);  // Clear text area
    M5.Display.setFont(&fonts::Font4);
    M5.Display.setTextColor(TFT_ORANGE, TFT_BLACK);
    M5.Display.setCursor(sliderX + sliderWidth + 8, bassY + 10);
    M5.Display.printf("%+d", bassDb);
  }
}

void loop() {
  M5.update();
  
  // Audio processing
  audioLoop();
  
  // Update battery indicator every 10 seconds (only when screen is on)
  if (!screenOff && millis() - lastBatteryUpdate > 10000) {
    lastBatteryUpdate = millis();
    // Redraw battery indicator area only
    int screenW = M5.Display.width();
    int batLevel = M5.Power.getBatteryLevel();
    bool isCharging = M5.Power.isCharging();
    int batX = screenW - 180;  // Match displayTrackList position
    int batY = 8;
    
    // Clear battery area (wider to cover old text)
    M5.Display.fillRect(batX - 5, batY - 5, 130, 30, TFT_BLACK);
    
    // Battery icon outline
    M5.Display.drawRect(batX, batY, 40, 20, TFT_WHITE);
    M5.Display.fillRect(batX + 40, batY + 5, 4, 10, TFT_WHITE);
    
    // Battery fill
    int fillW = 36 * batLevel / 100;
    uint16_t batColor = TFT_GREEN;
    if (batLevel <= 20) batColor = TFT_RED;
    else if (batLevel <= 50) batColor = TFT_YELLOW;
    if (fillW > 0) {
      M5.Display.fillRect(batX + 2, batY + 2, fillW, 16, batColor);
    }
    
    // Percentage
    M5.Display.setFont(&fonts::Font4);  // Bigger font for battery %
    M5.Display.setCursor(batX + 50, batY - 2);  // Match displayTrackList
    if (isCharging) {
      M5.Display.setTextColor(TFT_YELLOW, TFT_BLACK);
      M5.Display.printf("%d%%+", batLevel);
    } else {
      M5.Display.setTextColor(TFT_WHITE, TFT_BLACK);
      M5.Display.printf("%d%%", batLevel);
    }
  }
  
  // Update VU meters periodically when playing
  static unsigned long lastVUUpdate = 0;
  if (!screenOff && isPlaying() && !isPaused && millis() - lastVUUpdate > 50) {
    drawVUMeters();
    lastVUUpdate = millis();
  }
  
  // Decay VU meters when not playing
  if (!screenOff && (!isPlaying() || isPaused)) {
    if (vuLeft > 0 || vuRight > 0) {
      vuLeft = vuLeft > 5 ? vuLeft - 5 : 0;
      vuRight = vuRight > 5 ? vuRight - 5 : 0;
      if (millis() - lastVUUpdate > 50) {
        drawVUMeters();
        lastVUUpdate = millis();
      }
    }
  }
  
  // Touch handling
  if (M5.Touch.getCount() > 0) {
    auto touch = M5.Touch.getDetail();
    int x = touch.x;
    int y = touch.y;
    
    // If screen is off, require 3-second hold to wake up (prevent pocket activation)
    if (screenOff) {
      if (touch.isPressed()) {
        if (screenWakeTouchStart == 0) {
          screenWakeTouchStart = millis();  // Start timing
        } else if (millis() - screenWakeTouchStart >= 3000) {
          // Held for 3 seconds - wake up!
          screenOff = false;
          screenWakeTouchStart = 0;
          M5.Display.setBrightness(128);  // Restore brightness
          displayTrackList();  // Redraw UI
          delay(200);  // Debounce
        }
      } else {
        screenWakeTouchStart = 0;  // Reset if finger lifted
      }
      return;  // Don't process other touches while screen is off
    }
    
    int screenW = M5.Display.width();
    int screenH = M5.Display.height();
    int footerY = screenH - 300;  // 300px footer
    int trackListEndY = footerY;
    int trackListStartY = trackListStartY_g ? trackListStartY_g : 190;
    int lineHeight = trackLineHeight_g ? trackLineHeight_g : 30;
    
    // Slider positions - THICKER with MORE spacing
    int sliderX = 55;
    int sliderWidth = screenW - 130;
    int sliderH = 40;  // THICKER
    int sliderSpacing = 50;  // DOUBLE spacing
    int volY = footerY + 35;  // After track name row
    int trebY = volY + sliderSpacing;
    int bassY = trebY + sliderSpacing;
    
    // Control button positions (Row 4)
    int btnY = bassY + sliderSpacing + 5;
    int btnH = 55;  // BIGGER buttons
    int btnW = 90;
    int btnSpacing = 8;
    int startX = 5;
    int prevX = startX + btnW + btnSpacing;
    int playX = prevX + btnW + btnSpacing;
    int playW = 110;
    int nextX = playX + playW + btnSpacing;
    int shufX = nextX + btnW + btnSpacing;
    int smallBtnW = 70;
    int rptX = shufX + smallBtnW + btnSpacing;
    int loudX = rptX + smallBtnW + btnSpacing;
    int toggleX = screenW - 65;
    
    // Pagination position (Row 5)
    int navY = btnY + btnH + 12;
    int navBtnW = 110;
    int navBtnH = 50;
    
    if (touch.wasPressed()) {
      // Check for Screen OFF button in header (top right corner)
      int btnOffX = screenW - 45;
      int btnOffY = 5;
      if (x >= btnOffX && x <= btnOffX + 40 && y >= btnOffY && y <= btnOffY + 30) {
        screenOff = true;
        M5.Display.setBrightness(0);  // Turn off backlight
        delay(200);  // Debounce
        return;
      }
      
      // Check if touch is in footer area
      if (y >= footerY) {
        // Row 1: Volume slider
        if (y >= volY && y <= volY + sliderH) {
          volumeDragging = true;
          handleVolumeSlider(x);
        }
        // Row 2: Treble slider
        else if (y >= trebY && y <= trebY + sliderH) {
          trebleDragging = true;
          handleTrebleSlider(x);
        }
        // Row 3: Bass slider
        else if (y >= bassY && y <= bassY + sliderH) {
          bassDragging = true;
          handleBassSlider(x);
        }
        // Row 4: Control buttons
        else if (y >= btnY && y <= btnY + btnH) {
          // STOP button
          if (x >= startX && x <= startX + btnW) {
            stopPlayback();
            displayTrackList();
          }
          // PREV button
          else if (x >= prevX && x <= prevX + btnW) {
            playPrevious();
          }
          // PLAY/PAUSE button
          else if (x >= playX && x <= playX + playW) {
            togglePlayPause();
          }
          // NEXT button
          else if (x >= nextX && x <= nextX + btnW) {
            playNext();
          }
          // SHUFFLE button
          else if (x >= shufX && x <= shufX + smallBtnW) {
            shuffleMode = !shuffleMode;
            drawFooter();
          }
          // REPEAT button
          else if (x >= rptX && x <= rptX + smallBtnW) {
            repeatMode = (repeatMode + 1) % 3;
            drawFooter();
          }
          // LOUDNESS button
          else if (x >= loudX && x <= loudX + smallBtnW) {
            loudnessMode = !loudnessMode;
            drawFooter();
          }
          // SPK/HP toggle button
          else if (x >= toggleX && x <= toggleX + 55) {
            toggleAudioOutput();
          }
        }
        // Row 5: Pagination buttons
        else if (y >= navY && y <= navY + navBtnH) {
          // Previous page button
          if (x >= 10 && x <= 10 + navBtnW) {
            if (currentPage > 0) {
              displayStartIndex -= TRACKS_PER_PAGE;
              if (displayStartIndex < 0) displayStartIndex = 0;
              displayTrackList();
            }
          }
          // Next page button
          else if (x >= screenW - navBtnW - 10 && x <= screenW - 10) {
            if (currentPage < totalPages - 1) {
              displayStartIndex += TRACKS_PER_PAGE;
              displayTrackList();
            }
          }
        }
      }
      // Check if touch is in track list area (with debouncing)
      else if (y >= trackListStartY && y < trackListEndY) {
        unsigned long now = millis();
        if (now - lastTrackTouchTime > TRACK_TOUCH_DEBOUNCE) {
          int touchedLine = (y - trackListStartY) / lineHeight;
          int touchedIndex = displayStartIndex + touchedLine;
          
          // Only allow selection of visible tracks
          if (touchedLine < TRACKS_PER_PAGE && touchedIndex < trackList.size()) {
            lastTrackTouchTime = now;
            isPaused = false;
            playTrack(touchedIndex);
          }
        }
      }
    }
    // Slider drag (smooth following)
    else if (touch.isHolding()) {
      if (volumeDragging) handleVolumeSlider(x);
      else if (trebleDragging) handleTrebleSlider(x);
      else if (bassDragging) handleBassSlider(x);
    }
    // Release drag
    else if (touch.wasReleased()) {
      volumeDragging = false;
      trebleDragging = false;
      bassDragging = false;
    }
  }
  
  // Scroll handling with swipe (keep for convenience)
  if (M5.Touch.getCount() > 0) {
    auto touch = M5.Touch.getDetail();
    if (touch.wasFlicked()) {
      int deltaY = touch.distanceY();
      if (deltaY > 50) {
        // Swipe down - previous page
        if (displayStartIndex > 0) {
          displayStartIndex -= TRACKS_PER_PAGE;
          if (displayStartIndex < 0) displayStartIndex = 0;
          displayTrackList();
        }
      } else if (deltaY < -50) {
        // Swipe up - next page
        if (displayStartIndex + TRACKS_PER_PAGE < trackList.size()) {
          displayStartIndex += TRACKS_PER_PAGE;
          displayTrackList();
        }
      }
    }
  }
  
  delay(10);
}
