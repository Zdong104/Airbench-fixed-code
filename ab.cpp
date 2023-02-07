// AB.CPP

//--------------------------------------------------------------------

const char VERSION[] = "2.50";

char RunVersion[80] = "";

//--------------------------------------------------------------------

static double Trunc( double d, double precision )
{
   return static_cast<long long>(d/precision)*precision;
}

#include <carstuff.hpp>
#include <mmsystem.h>
#include <gpib.hpp>
#include "lanname.hpp"
#include "ab.h"

#include <errno.h>
#include <fcntl.h>
#include <io.h>
#include <sys/stat.h>

static HINSTANCE hinst = 0;

static GpibClass gpib;

//--------------------------------------------------------------------

static char exepath[_MAX_PATH] = { 0 };

//--------------------------------------------------------------------

const int POWER_READ_DELAY = 100;

const int MAXFILES = 10;
const int MAXINCREMENTS = 100;

const int VALVE_DELAY_SECONDS = 30;

static char LAN = 'T';
static char filename[MAXFILES][_MAX_PATH] = { 0 };
// static char mostrecentoverlayfilename[_MAX_PATH] = "";
static char lanfilename[_MAX_PATH] = "";
static bool bSaveFile = false;
static bool bSaveFileToLan = false;
static bool bUnsavedData = false;
static bool bUsed[MAXFILES] = { 0 };
static int IC[MAXFILES] = { 0 };
static int ICgraph[MAXFILES] = { 0 };

static double CFM[MAXFILES][MAXINCREMENTS], PRESUR[MAXFILES][MAXINCREMENTS];
static double RPM[MAXFILES], SMM[MAXFILES], VDC[MAXFILES], PWM[MAXFILES];
static char FANORBOX[MAXFILES][58+1], DT[MAXFILES][10+1];
static char ACDC[MAXFILES][1+1], HE[MAXFILES][1+1], TYPE[MAXFILES][1+1];
static bool withPower[MAXFILES];
static double VOLTS[MAXFILES][MAXINCREMENTS], AMPS[MAXFILES][MAXINCREMENTS], WATTS[MAXFILES][MAXINCREMENTS];

const double minVDC = 4;
const double maxVDC = 999.9;
const int maxlengthVDC = 5;
const char formatVDC[] = "%.1f";
const double precisionVDC = 0.1;

const int minRPM = 100;
const int maxRPM = 20000;
const int maxlengthRPM = 5;
const char formatRPM[] = "%d";
const int incrementRPM = 10;

const int minPWM = 0;
const int maxPWM = 100;
const int maxlengthPWM = 3;
const char formatPWM[] = "%d";
const int incrementPWM = 1;

static bool bIsSystemFan = false;

static const char* pargv = 0;

static HWND hwndMain = 0;
static HWND hwndDlgRun = 0;

static HFONT hfontFixed = 0;

// static bool bBestFitCurve = true;
const bool bBestFitCurve = false;

static bool DEMO = false;
static bool NOINIT = false;

static const double PRESSURE_LIMIT = 4;

//--------------------------------------------------------------------

static bool SkipStep( int i )
{
   if ( IC[i] == 1 )
   {
      if ( CFM[i][0] == 0 )
      {
         if ( CFM[i][1] == 0 )
         {
            return true;
         }
      }
   }
   return false;
}

//--------------------------------------------------------------------

double LL = BADFLOAT;
const double min_LL = 2;
const double max_LL = 2000;
const int maxlength_LL = 4;
const char format_LL[] = "%.0f";
const double precision_LL = 1;
static bool IsValidFor_LL( double d )
{
   return IsValid(d);
}

double bb = BADFLOAT;
const double min_bb = 1.0000000001;
const double max_bb = 499.9999999999;
const int maxlength_bb = 14;
const char format_bb[] = "%.10f";
const double precision_bb = 0.0000000001;
static bool IsValidFor_bb( double d )
{
   return IsValid(d);
}

double cc = BADFLOAT;
const double min_cc = -9.9999999999;
const double max_cc = +9.9999999999;
const int maxlength_cc = 13;
const char format_cc[] = "%.10f";
const double precision_cc = 0.0000000001;
static bool IsValidFor_cc( double d )
{
   return IsValid(d) && ( d != 0 );
}

double vv = BADFLOAT;
double vvstat = BADFLOAT;
const double min_vv = 1.0;
const double max_vv = 24.8;
const int maxlength_vv = 4;
const char format_vv[] = "%.1f";
const double precision_vv = 0.1;
static bool IsValidFor_vv( double d )
{
   return IsValid(d);
}

double pp = BADFLOAT;
double ppstat = BADFLOAT;
const double min_pp = 1.0;
const double max_pp = 24.8;
const int maxlength_pp = 4;
const char format_pp[] = "%.1f";
const double precision_pp = 0.1;
static bool IsValidFor_pp( double d )
{
   return IsValid(d);
}

double off = BADFLOAT;
double offstat = BADFLOAT;
const double min_off = -24.0;
const double max_off = +24.0;
const int maxlength_off = 8;
const char format_off[] = "%.4f";
const double precision_off = 0.0001;
static bool IsValidFor_off( double d )
{
   return IsValid(d);
}

static bool IsConfigured()
{
   if ( ! IsValidFor_LL(LL) )
   {
      return false;
   }
   if ( ! IsValidFor_bb(bb) )
   {
      return false;
   }
   if ( ! IsValidFor_cc(cc) )
   {
      return false;
   }
   if ( ! IsValidFor_vv(vv) )
   {
      return false;
   }
   if ( ! IsValidFor_vv(vvstat) )
   {
      return false;
   }
   if ( ! IsValidFor_pp(pp) )
   {
      return false;
   }
   if ( ! IsValidFor_pp(ppstat) )
   {
      return false;
   }
   if ( ! IsValidFor_off(off) )
   {
      return false;
   }
   if ( ! IsValidFor_off(offstat) )
   {
      return false;
   }
   return true;
}

inline double CalcCFM( double xx )
{
   const double KK = ( xx - off ) * pp / vv;
   const double cfm = bb*KK + cc*KK*KK;
   return cfm;
}

inline double CalcPressure( double xx )
{
   const double pressure = ( xx - offstat ) * ppstat / vvstat;
   return pressure;
}

//--------------------------------------------------------------------

namespace
{
   enum AbTypeConstant
   {
      ABTYPE_001 = 1,
      ABTYPE_002 = 2,
   };
};

static AbTypeConstant AbType = ABTYPE_002;

static void ReadAbType()
{
   char abtypefilename[_MAX_PATH] = { 0 };
   sprintfsafe( abtypefilename, sizeof(abtypefilename), "%s%s", exepath, "$ABTYPE$.$$$" );

   FILE* pf = fopen( abtypefilename, "r" );
   if ( pf )
   {
      char buffer[80] = "";
      if ( getline( buffer, sizeof(buffer), pf ) )
      {
         const int value = StringToInt(buffer);
         if ( IsValid(value) )
         {
            AbType = static_cast<AbTypeConstant>(value);
         }
      }
      fclose( pf );
   }
}

static void WriteAbType()
{
   char cfgfilename[_MAX_PATH] = { 0 };
   sprintfsafe( cfgfilename, sizeof(cfgfilename), "%s%s", exepath, "$ABTYPE$.$$$" );

   FILE* pf = fopen( cfgfilename, "w" );
   if ( pf )
   {
      fprintf( pf, "%d\n", static_cast<int>(AbType) );
      fclose( pf );
   }
}

//--------------------------------------------------------------------

static double PulseTimeInterval[MAXFILES];

const double minPULSETIME = 0;
const double maxPULSETIME = 5;
const int maxlengthPULSETIME = 10;
const char formatPULSETIME[] = "%.3f";
const double precisionPULSETIME = 0.001;

static double DefaultPulseTimeInterval( char curTYPE )
{
   switch ( curTYPE )
   {
      case 'i':
      {
         return 0.05;
         break;
      }
      case 'r':
      {
         return 0;
         break;
      }
      case 'f':
      {
         return 0.10;
         break;
      }
   }
   return BADFLOAT;
}

//--------------------------------------------------------------------

#define WM_USER_RUN_UPDATE_STATUS   WM_USER+0x8001
#define WM_USER_RUN_COMPLETE        WM_USER+0x8002
#define WM_USER_RUN_STOPPED         WM_USER+0x8003
#define WM_USER_EXIT                WM_USER+0x8004
#define WM_USER_RUN_DIED            WM_USER+0x8005
#define WM_USER_RUN_INTERRUPTED     WM_USER+0x8006
#define WM_USER_RUN_OKON            WM_USER+0x8007
#define WM_USER_RUN_OKOFF           WM_USER+0x8008

//--------------------------------------------------------------------

static MutexClass Mutex;

//--------------------------------------------------------------------

static double XINT, YINT, IX, IY, XMAX, YMAX;

static double CFMSCALE, PRESURSCALE;

const int maxlengthCFMSCALE = 10;
const char formatCFMSCALE[] = "%.0f";
const double precisionCFMSCALE = 1;
const double ultimatemaxallowedCFMSCALE = 200;
static double minallowedCFMSCALE;
static double maxallowedCFMSCALE;

const int maxlengthPRESURSCALE = 10;
const char formatPRESURSCALE[] = "%.2f";
const double precisionPRESURSCALE = 0.01;
const double ultimatemaxallowedPRESURSCALE = 0.30;
static double minallowedPRESURSCALE;
static double maxallowedPRESURSCALE;

static void CalculateScaleStuff()
{
   if ( PRESURSCALE > .7 )
   {
      YINT=.1;
   }
   else if ( PRESURSCALE > .2 )
   {
      YINT=.05;
   }
   else
   {
      YINT=.01;
   }

   // <10=0.5   <20=1.0   <40=2   <100=5    <400=20    else=100
   if ( CFMSCALE < 10 )
   {
      XINT=0.5;
   }
   else if ( CFMSCALE < 20 )
   {
      XINT=1;
   }
   else if ( CFMSCALE < 40 )
   {
      XINT=2;
   }
   else if ( CFMSCALE < 100 )
   {
      XINT=5;
   }
   else if ( CFMSCALE < 400 )
   {
      XINT=20;
   }
   else
   {
      XINT=100;
   }

   IX=static_cast<int>((CFMSCALE+XINT-precisionCFMSCALE/10)/XINT);
   IY=static_cast<int>((PRESURSCALE+YINT-precisionPRESURSCALE/10)/YINT);

   XMAX=IX*XINT;
   YMAX=IY*YINT;
}

//--------------------------------------------------------------------

static double A[MAXFILES], B[MAXFILES];
static int M[MAXFILES] = { 0 };

static void Calculate()
{
   memcpy( ICgraph, IC, sizeof(ICgraph) );
   {
      for ( int i = 0; i < MAXFILES; ++i )
      {
         if ( ! bUsed[i] )
         {
            continue;
         }
         switch ( TYPE[i][0] )
         {
            case 'f':
            {
               {
                  for ( int j = 0; j < IC[i]; ++j )
                  {
                     if ( PRESUR[i][j] <= 0 )
                     {
                        ICgraph[i] = j + 1;
                        break;
                     }
                  }
               }
               break;
            }
         }
      }
   }

   // Determine maximum CFM, pressure
   double CMAX = 0;
   double PMAX = 0;
   {
      for ( int i = 0; i < MAXFILES; ++i )
      {
         if ( ! bUsed[i] )
         {
            continue;
         }
         {
            for ( int j = 0; j < ICgraph[i]; ++j )
            {
               if ( CFM[i][j]>CMAX )
               {
                  CMAX=CFM[i][j];
               }
               if ( fabs(PRESUR[i][j])>PMAX )
               {
                  PMAX=fabs(PRESUR[i][j]);
               }
            }
         }
      }
   }

   // Adjust the data
   {
      for ( int i = 0; i < MAXFILES; ++i )
      {
         if ( ! bUsed[i] )
         {
            continue;
         }
         switch ( TYPE[i][0] )
         {
            case 'f':
            {
               {
                  bool bFirstTime = true;
                  {
                     for ( int j = 0; j < ICgraph[i]; ++j, bFirstTime = false )
                     {
                        if ( ! bFirstTime )
                        {
                           if ( PRESUR[i][j]*PRESUR[i][j-1]<0 )
                           {
                              CFM[i][j] -= ((CFM[i][j-1]-CFM[i][j])/(PRESUR[i][j-1]-CFM[i][j]))*PRESUR[i][j];
                              PRESUR[i][j] = 0;
                           }
                        }
                     }
                  }
               }
               break;
            }
         }
      }
   }

   // best fit curve for I test
   {
      for ( int i = 0; i < MAXFILES; ++i )
      {
         if ( ! bUsed[i] )
         {
            continue;
         }
         switch ( TYPE[i][0] )
         {
            case 'i':
            {
               {
                  int N=0;
                  double EX=0, EY=0, EX2=0, EY2=0, EXY=0;
                  {
                     for ( int j = 0; j < ICgraph[i]; ++j )
                     {
                        if ( ( j == 0 ) || ( CFM[i][j]<10 ) )
                        {
                           ++N;
                        }
                        else
                        {
                           const double Y=log(fabs(PRESUR[i][j]-PRESUR[i][0]));
                           const double X=log(CFM[i][j]);

                           EX += X;
                           EY += Y;
                           EX2 += pow(X,2);
                           EY2 += pow(Y,2);
                           EXY += X*Y;

                        }
                     }
                  }

                  M[i]=ICgraph[i]-N;

                  if ( M[i] > 0 )
                  {
                     B[i]=(M[i]*EXY-EX*EY)/(M[i]*EX2-pow(EX,2));
                     A[i]=exp((EY-B[i]*EX)/M[i]);
                  }
                  else
                  {
                     A[i] = 0;
                     B[i] = 0;
                  }
               }
               break;
            }
         }
      }
   }

   CFMSCALE = CMAX;
   PRESURSCALE = PMAX;
   CalculateScaleStuff();
   CFMSCALE = XMAX;
   PRESURSCALE = YMAX;
   minallowedCFMSCALE=CFMSCALE;
   minallowedPRESURSCALE=PRESURSCALE;
   maxallowedCFMSCALE=max(minallowedCFMSCALE,ultimatemaxallowedCFMSCALE);
   maxallowedPRESURSCALE=max(minallowedPRESURSCALE,ultimatemaxallowedPRESURSCALE);
}

//--------------------------------------------------------------------

static bool WriteFile( const char* outfilename )
{
   const int i = 0;

   FILE*const pf = fopen( outfilename, "w" );
   if ( ! pf )
   {
      return false;
   }

   char line[_MAX_PATH] = "";

   {
      sprintfsafe( line, sizeof(line), "%d", IC[i] );
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return false;
      }
   }

   {
      for ( int j = 0; j < IC[i]; ++j )
      {
         sprintfsafe( line, sizeof(line), "%.3f,%.4f,0,0,0", CFM[i][j], PRESUR[i][j] );
         if ( withPower[i] )
         {
            sprintfsafecat( line, sizeof(line), ",%.2f", VOLTS[i][j] );
            sprintfsafecat( line, sizeof(line), ",%.2f", AMPS[i][j] );
            sprintfsafecat( line, sizeof(line), ",%.3f", WATTS[i][j] );
         }
         if ( fprintf( pf, "%s\n", line ) < 0 )
         {
            fclose( pf );
            return false;
         }
      }
   }

   {
      sprintfsafe( line, sizeof(line), "%.1f,0,0,0,0,0", VDC[i] );
      if ( bIsSystemFan )
      {
         strcatarray( line, ",SYSTEMFAN" );
      }
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return false;
      }
   }

   {
      sprintfsafe( line, sizeof(line), "\"%s\",\"%s\",\"%s\",\"%s\",\"%s\",\"%.0f\",\"%.0f\"",
                   FANORBOX[i], TYPE[i], HE[i], DT[i], ACDC[i], RPM[i], SMM[i] );
      sprintfsafecat( line, sizeof(line), ",\"%.3f\"", PulseTimeInterval[i] );
      sprintfsafecat( line, sizeof(line), ",\"%.0f\"", PWM[i] );
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return false;
      }
   }

   {
      strcpyarray( line, RunVersion );
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return false;
      }
   }

   if ( fclose( pf ) != 0 )
   {
      return false;
   }

   return true;
}

static void SaveFileToLan()
{
   if ( ! bSaveFileToLan )
   {
      return;
   }
   if ( ! WriteFile(lanfilename) )
   {
      MsgOkError( "Error!", "Could not write to LAN file\n\n%s", lanfilename );
      return;
   }
}

static bool GetSaveName()
{
   const int i = 0;

   char cwd[_MAX_PATH] = "";
   getcwd( cwd, sizeof(cwd) );
   OPENFILENAME ofn = { 0 };
   {
      char* ext = 0;
      char filters[80*1] = "";
      {
         int offset = 0;
         switch ( TYPE[i][0] )
         {
            case 'i':
            {
               ext = "IMP";
               offset += sprintfsafe( filters+offset, sizeof(filters)-offset, "%s (%s)%c%s%c", "IMP"    , "*.imp"        , '\0', "*.imp"        , '\0' );
               break;
            }
            case 'r':
            {
               ext = "RAT";
               offset += sprintfsafe( filters+offset, sizeof(filters)-offset, "%s (%s)%c%s%c", "RAT"    , "*.rat"        , '\0', "*.rat"        , '\0' );
               break;
            }
            case 'f':
            {
               ext = "FAN";
               offset += sprintfsafe( filters+offset, sizeof(filters)-offset, "%s (%s)%c%s%c", "FAN"    , "*.fan"        , '\0', "*.fan"        , '\0' );
               break;
            }
         }
      }
      ofn.lStructSize = sizeof(ofn);
      ofn.lpstrFilter = filters;
      ofn.hwndOwner = hwndMain;
      ofn.lpstrFile = filename[i];
      ofn.nMaxFile = sizeof(filename[i]);
      ofn.lpstrTitle = "Save results to...";
      ofn.lpstrDefExt = ext;
      ofn.Flags = OFN_OVERWRITEPROMPT | OFN_HIDEREADONLY | OFN_NOCHANGEDIR;
   }
   if ( ! *ofn.lpstrFile )
   {
      ofn.lpstrInitialDir = cwd;
   }

   for (;;)
   {
      if ( ! GetSaveFileName( &ofn ) )
      {
         return bSaveFile;
      }

      FILE*const pf = fopen( filename[i], "w" );
      if ( ! pf )
      {
         MsgOkError( "Error!", "Could not write to file\n\n%s", filename[i] );
         continue;
      }
      fclose( pf );

      bSaveFile = true;
      return bSaveFile;
   }
}

static bool SaveFile()
{
   const int i = 0;
   if ( ! bSaveFile )
   {
      return false;
   }
   if ( ! WriteFile(filename[i]) )
   {
      MsgOkError( "Error!", "Could not write to file\n\n%s", filename[i] );
      return false;
   }
   bUnsavedData = false;
   SaveFileToLan();
   return true;
}

static void UpdateWindowTitle()
{
   const int i = 0;
   const char* p = "";
   if ( *filename[i] )
   {
      p = strrchr( filename[i], '\\' );
      if ( p )
      {
         ++p;
      }
      else
      {
         p = filename[i];
      }
   }
   SetWindowTextf( hwndMain, "AirBench %s - %s", VERSION, p );
}

static bool HandleUnsavedData()
{
   if ( ! bUnsavedData )
   {
      return true;
   }
   for (;;)
   {
      const int rc = MsgYesNoCancelWarning( "Data not saved!",
         "Current data has not been saved!\n\nDo you want to save current data to disk before it is discarded?" );

      if ( MsgIsYes(rc) )
      {
         bSaveFile = GetSaveName();
         if ( bSaveFile )
         {
            bSaveFileToLan = GetLanName( hinst, hwndMain, filename[0], LAN, lanfilename, sizeof(lanfilename) );
         }
         if ( SaveFile() )
         {
            UpdateWindowTitle();
            return true;
         }
      }
      else if ( MsgIsNo(rc) )
      {
         UpdateWindowTitle();
         return true;
      }
      else
      {
         UpdateWindowTitle();
         return false;
      }
   }
}

static bool ReadFile( int i, const char* newfilename )
{
   stringblank( RunVersion );
   Mutex.Request();
   bUsed[i] = false;
   Mutex.Release();

   strcpyarray( filename[i], newfilename );

   FILE*const pf = fopen( filename[i], "r" );
   if ( ! pf )
   {
      MsgOkError( "Error!", "Could not open file\n\n%s", filename[i] );
      return false;
   }

   const char tokens[] = ",\n";
   char line[_MAX_PATH] = "";

   IC[i] = 0;
   withPower[i] = false;

   {
      if ( ! fgets( line, sizeof(line), pf ) )
      {
         fclose( pf );
         return true;
      }

      char* ptr = strtok( line, tokens );
      int ICTEMP = StringToInt( ptr );
      if ( ! IsValid(ICTEMP) )
      {
         fclose( pf );
         return true;
      }

      {
         for ( int k = 0; k < ICTEMP; ++k )
         {
            const int j = IC[i];

            if ( ! fgets( line, sizeof(line), pf ) )
            {
               fclose( pf );
               return true;
            }

            ptr = strtok( line, tokens );
            CFM[i][j] = StringToFloat( ptr, 0.001 );
            if ( ! IsValid(CFM[i][j]) )
            {
               fclose( pf );
               return true;
            }

            ptr = strtok( NULL, tokens );
            PRESUR[i][j] = StringToFloat( ptr, 0.0001 );
            if ( ! IsValid(PRESUR[i][j]) )
            {
               fclose( pf );
               return true;
            }

            ptr = strtok( NULL, tokens );
            ptr = strtok( NULL, tokens );
            ptr = strtok( NULL, tokens );

            VOLTS[i][j] = -1;
            ptr = strtok( NULL, tokens );
            if ( ptr )
            {
               VOLTS[i][j] = StringToFloat( ptr, 0.01 );
               if ( ! IsValid(VOLTS[i][j]) )
               {
               }
               if ( j == 0 )
               {
                  withPower[i] = true;
               }
            }

            AMPS[i][j] = -1;
            ptr = strtok( NULL, tokens );
            if ( ptr )
            {
               AMPS[i][j] = StringToFloat( ptr, 0.01 );
               if ( ! IsValid(AMPS[i][j]) )
               {
               }
            }

            WATTS[i][j] = -1;
            ptr = strtok( NULL, tokens );
            if ( ptr )
            {
               WATTS[i][j] = StringToFloat( ptr, 0.001 );
               if ( ! IsValid(WATTS[i][j]) )
               {
               }
            }

            Mutex.Request();
            if ( ! SkipStep( i ) )
            {
               ++IC[i];
            }
            Mutex.Release();
         }
      }
   }

   {
      if ( ! fgets( line, sizeof(line), pf ) )
      {
         fclose( pf );
         return true;
      }

      char* ptr = strtok( line, tokens );
      VDC[i] = StringToFloat( ptr, 0.1 );
      if ( ! IsValid(VDC[i]) )
      {
         fclose( pf );
         return true;
      }

      {
         for ( int j = 0; j < 5; ++j )
         {
            strtok( NULL, tokens );
         }
      }

      bIsSystemFan = false;
      ptr = strtok( NULL, tokens );
      if ( ptr )
      {
         if ( strcmp( ptr, "SYSTEMFAN" ) == 0 )
         {
            bIsSystemFan = true;
         }
      }
   }

   {
      if ( ! fgets( line, sizeof(line), pf ) )
      {
         fclose( pf );
         return true;
      }

      char* ptr = strstr( line, "\"," );
      if ( ! ptr )
      {
         fclose( pf );
         return true;
      }
      *ptr = '\0';                           // strip end quote
      strcpyarray( FANORBOX[i], line+1 );    // skip first quote
      ++ptr;
      ++ptr;

      ptr = strtok( ptr, tokens );
      ++ptr;                        // skip first quote
      ptr[strlen(ptr)-1] = '\0';    // strip end quote
      TYPE[i][0] = tolower(*ptr);
      TYPE[i][1] = '\0';

      ptr = strtok( NULL, tokens );
      ++ptr;                        // skip first quote
      ptr[strlen(ptr)-1] = '\0';    // strip end quote
      HE[i][0] = toupper(*ptr);
      HE[i][1] = '\0';

      ptr = strtok( NULL, tokens );
      ++ptr;                        // skip first quote
      ptr[strlen(ptr)-1] = '\0';    // strip end quote
      strcpyarray( DT[i], ptr );

      ptr = strtok( NULL, tokens );
      ++ptr;                        // skip first quote
      ptr[strlen(ptr)-1] = '\0';    // strip end quote
      ACDC[i][0] = toupper(*ptr);
      ACDC[i][1] = '\0';

      ptr = strtok( NULL, tokens );
      ++ptr;                        // skip first quote
      ptr[strlen(ptr)-1] = '\0';    // strip end quote
      RPM[i] = StringToFloat( ptr, 1 );
      if ( ! IsValid(RPM[i]) )
      {
         fclose( pf );
         return true;
      }

      ptr = strtok( NULL, tokens );
      ++ptr;                        // skip first quote
      ptr[strlen(ptr)-1] = '\0';    // strip end quote
      SMM[i] = StringToFloat( ptr, 1 );
      if ( ! IsValid(SMM[i]) )
      {
         fclose( pf );
         return true;
      }

      PulseTimeInterval[i] = DefaultPulseTimeInterval( TYPE[i][0] );
      ptr = strtok( NULL, tokens );
      if ( ptr )
      {
         ++ptr;                        // skip first quote
         ptr[strlen(ptr)-1] = '\0';    // strip end quote
         PulseTimeInterval[i] = StringToFloat( ptr, 0.001 );
         if ( ! IsValid(PulseTimeInterval[i]) )
         {
            fclose( pf );
            return true;
         }
      }

      PWM[i] = -1;
      ptr = strtok( NULL, tokens );
      if ( ptr )
      {
         ++ptr;                        // skip first quote
         ptr[strlen(ptr)-1] = '\0';    // strip end quote
         PWM[i] = StringToFloat( ptr, 1 );
         if ( ! IsValid(PWM[i]) )
         {
            fclose( pf );
            return true;
         }
      }

   }

   if ( getline( line, sizeof(line), pf ) )
   {
      strcpyarray( RunVersion, line );
   }

   fclose( pf );

   Mutex.Request();
   bUsed[i] = true;
   Calculate();
   Mutex.Release();
   return true;
}

//--------------------------------------------------------------------

const COLORREF aColor[MAXFILES] =
{
   CLR_RED       ,
   CLR_DARKBLUE  ,
   CLR_DARKPINK  ,
   CLR_DARKGREEN ,
   CLR_DARKCYAN  ,
   CLR_BROWN     ,
   CLR_DARKRED   ,
   CLR_PINK      ,
   CLR_GREEN     ,
   CLR_CYAN      ,
};

const char aMarker[MAXFILES] =
{
   'x',
   '1',
   '2',
   '3',
   '4',
   '5',
   '6',
   '7',
   '8',
   '9',
};

static double FNISCL( double X, double P1, double P2, double U1, double U2 )
{
   return X*((P2-P1)/(U2-U1))-U1*(P2-P1)/(U2-U1);
}

static char FIG[16+1]="", YOURNAM[26+1]="";

static char fontname[80] = "";
static bool bBold = false;
static bool bItalic = false;
static int fontsize = 8;

namespace
{
   struct DrawGraphStruct
   {
      const bool bPermanent;
      const bool bPrinting;

      explicit DrawGraphStruct( bool inbPermanent, bool inbPrinting ) :
         bPermanent(inbPermanent),
         bPrinting(inbPrinting)
      {
      }

   private:

      explicit DrawGraphStruct(const DrawGraphStruct&);
      DrawGraphStruct& operator=(const DrawGraphStruct&);

   };
}

static void DrawGraph( HDC hdc, SIZE size, void* arg )
{
   Mutex.Request();

   SetBkMode( hdc, TRANSPARENT );

   DrawGraphStruct*const pdgs = reinterpret_cast<DrawGraphStruct*>( arg );

   const HFONT hfont = CreateFont( hdc, fontname, fontsize, bBold, bItalic );
   const HFONT hfontOld = SelectFont( hdc, hfont );

   EASYTEXTMETRICS etm( hdc );

   if ( pdgs->bPermanent && ! pdgs->bPrinting )
   {
      const HPEN hpen = CreatePen( PS_SOLID, 1, CLR_WHITE );
      winassert( hpen );
      const HBRUSH hbrush = CreateSolidBrush( CLR_WHITE );
      winassert( hbrush );
      const HPEN hpenOld = SelectPen( hdc, hpen );
      const HBRUSH hbrushOld = SelectBrush( hdc, hbrush );
      {
         Rectangle( hdc, 0, 0, size.cx, size.cy );
      }
      SelectBrush( hdc, hbrushOld );
      SelectPen( hdc, hpenOld );
      DeleteBrush( hbrush );
      DeletePen( hpen );
   }

   const double XLEFT = size.cx*2/16;
   const double XRIGHT = size.cx*15/16;
   const double YTOP = size.cy*2/16;
   const double YBOTTOM = size.cy*13/16;

   const double TMX = (XRIGHT-XLEFT)/IX;
   const double TMY = (YBOTTOM-YTOP)/IY;

   bool bDataPresent = false;
   {
      for ( int i = 0; i < MAXFILES; ++i )
      {
         if ( bUsed[i] && ( IC[i] > 0 ) )
         {
            bDataPresent = true;
            break;
         }
      }
   }

   if ( bDataPresent )
   {
      // Draw the axes
      {
         {
            for ( int j = 0; j <= IX; ++j )
            {
               {
                  POINT pt = { static_cast<LONG>(XLEFT+j*TMX), static_cast<LONG>(YBOTTOM) };
                  MoveToEx( hdc, pt.x, pt.y, 0 );
               }
               {
                  POINT pt = { static_cast<LONG>(XLEFT+j*TMX), static_cast<LONG>(YBOTTOM-IY*TMY) };
                  LineTo( hdc, pt.x, pt.y );
               }
               if ( j < IX )
               {
                  for ( int k = 1; k <= 3; ++k )
                  {
                     {
                        POINT pt = { static_cast<LONG>(XLEFT+j*TMX+k*TMX/4), static_cast<LONG>(YBOTTOM-fontsize/2) };
                        MoveToEx( hdc, pt.x, pt.y, 0 );
                     }
                     {
                        POINT pt = { static_cast<LONG>(XLEFT+j*TMX+k*TMX/4), static_cast<LONG>(YBOTTOM+fontsize/2) };
                        LineTo( hdc, pt.x, pt.y );
                     }
                  }
               }
            }
         }

         {
            for ( int j = 0; j <= IY; ++j )
            {
               {
                  POINT pt = { static_cast<LONG>(XLEFT), static_cast<LONG>(YBOTTOM-j*TMY) };
                  MoveToEx( hdc, pt.x, pt.y, 0 );
               }
               {
                  POINT pt = { static_cast<LONG>(XLEFT+IX*TMX), static_cast<LONG>(YBOTTOM-j*TMY) };
                  LineTo( hdc, pt.x, pt.y );
               }
               if ( j < IY )
               {
                  for ( int k = 1; k <= 3; ++k )
                  {
                     {
                        POINT pt = { static_cast<LONG>(XLEFT-fontsize/2), static_cast<LONG>(YBOTTOM-j*TMY-k*TMY/4) };
                        MoveToEx( hdc, pt.x, pt.y, 0 );
                     }
                     {
                        POINT pt = { static_cast<LONG>(XLEFT+fontsize/2), static_cast<LONG>(YBOTTOM-j*TMY-k*TMY/4) };
                        LineTo( hdc, pt.x, pt.y );
                     }
                  }
               }
            }
         }
      }

      // Label axes
      {
         {
            for ( int j = 0; j <= IY; ++j )
            {
               TextDrawRightAligned( hdc, static_cast<LONG>(XLEFT), static_cast<LONG>(YBOTTOM-j*TMY)-etm.cyAscent, "%.2f ", j*YINT );

            }
         }

         {
            for ( int j = 0; j <= IX; ++j )
            {
               TextDrawVerticalTopAligned( hdc, static_cast<LONG>(XLEFT+j*TMX)-etm.cyAscent, static_cast<LONG>(YBOTTOM), "%g ", j*XINT );

            }
         }
      }

      // Draw plot labels
      {
         const int i = 0;

         {
            switch ( TYPE[i][0] )
            {
               case 'i':
               {
                  if ( bBestFitCurve )
                  {
                     TextDrawRightAligned( hdc, static_cast<LONG>(XRIGHT-etm.cxAvgCaps/2), static_cast<LONG>(YTOP-etm.cySpaced*5/4), "Best fit curve: Static pressure = %.2e * CFM ^ %.2f + %.4f", A[i], B[i], fabs(PRESUR[i][0]) );
                  }
                  break;
               }
               case 'f':
               {
                  char buffer[80] = "";
                  strcpyarray( buffer, "Parameters: " );
                  if ( ! bIsSystemFan )
                  {
                     sprintfsafecat( buffer, sizeof(buffer), "%.1f vdc, ", VDC[i] );
                     if ( RPM[i] )
                     {
                        sprintfsafecat( buffer, sizeof(buffer), "%.0f RPM, ", RPM[i] );
                     }
                     if ( PWM[i] >= 0 )
                     {
                        sprintfsafecat( buffer, sizeof(buffer), "%.0f%% PWM duty cycle, ", PWM[i] );
                     }
                     if ( SMM[i] == -1 )
                     {
                        strcatarray( buffer, "Blower, " );
                     }
                     else
                     {
                        sprintfsafecat( buffer, sizeof(buffer), "%.0f mm, ", SMM[i] );
                     }
                  }
                  sprintfsafecat( buffer, sizeof(buffer), "%d steps", IC[i] );
                  TextDrawRightAligned( hdc, static_cast<LONG>(XRIGHT-etm.cxAvgCaps/2), static_cast<LONG>(YTOP-etm.cySpaced*5/4), "%s", buffer );
                  break;
               }
            }
         }

         {
            TextDrawVerticalCentered( hdc, static_cast<LONG>(XLEFT*3/8)-etm.cyAscent, static_cast<LONG>(YBOTTOM-(YBOTTOM-YTOP)/2), "INCHES OF WATER" );
         }

         {
            TextDraw( hdc, static_cast<LONG>(XLEFT/4), static_cast<LONG>(YBOTTOM+(size.cy-YBOTTOM)*3/8)-etm.cyAscent, "CFM ---->" );
         }

         {
            char name[sizeof(FANORBOX[0])] = "";
            strcpyarray( name, FANORBOX[i] );
            striptrailblanks( name );

            char prefix[20] = "";
            {
               switch ( TYPE[i][0] )
               {
                  case 'i':
                  {
                     strcpyarray( prefix, "Impedance" );
                     break;
                  }
                  case 'f':
                  {
                     strcpyarray( prefix, "Performance" );
                     break;
                  }
               }
            }
            TextDraw( hdc, static_cast<LONG>(XLEFT/4), static_cast<LONG>(YBOTTOM+(size.cy-YBOTTOM)*5/8)-etm.cyAscent, "%s curve for:  %s", prefix, name );
         }

         {
            TextDraw( hdc, static_cast<LONG>(XLEFT/4), static_cast<LONG>(YBOTTOM+(size.cy-YBOTTOM)*7/8)-etm.cyAscent, "Recorded: %s", DT[i] );
         }

         {
            char name[sizeof(FIG)] = "";
            strcpyarray( name, FIG );
            striptrailblanks( name );

            TextDrawCentered( hdc, static_cast<LONG>(size.cx/2), static_cast<LONG>(YBOTTOM+(size.cy-YBOTTOM)*7/8)-etm.cyAscent, "%s", name );
         }

         if ( *RunVersion )
         {
            TextDrawRightAligned( hdc, static_cast<LONG>(size.cx-XLEFT/4), static_cast<LONG>(YBOTTOM+(size.cy-YBOTTOM)*3/8)-etm.cyAscent, " AirBench %s", RunVersion );
         }

         {
            char name[sizeof(YOURNAM)] = "";
            strcpyarray( name, YOURNAM );
            striptrailblanks( name );

            TextDrawRightAligned( hdc, static_cast<LONG>(size.cx-XLEFT/4), static_cast<LONG>(YBOTTOM+(size.cy-YBOTTOM)*5/8)-etm.cyAscent, "%s", name );
         }

         {
            const time_t t = time(0);
            char buffer[2+1+2+1+4+1] = "";
            strftime( buffer, sizeof(buffer), "%m-%d-%Y", localtime(&t) );
            TextDrawRightAligned( hdc, static_cast<LONG>(size.cx-XLEFT/4), static_cast<LONG>(YBOTTOM+(size.cy-YBOTTOM)*7/8)-etm.cyAscent, "%s", buffer );
         }

      }

      // Plot the data
      {
         for ( int i = MAXFILES-1; i >= 0; --i )
         {
            if ( ! bUsed[i] )
            {
               continue;
            }

            const COLORREF colorOld = SetTextColor( hdc, aColor[i] );
            const HPEN hpen = CreatePen( PS_SOLID, 1, aColor[i] );
            winassert( hpen );
            const HPEN hpenOld = SelectPen( hdc, hpen );

            {
               const char* p = strrchr( filename[i], '\\' );
               if ( p )
               {
                  ++p;
               }
               else
               {
                  p = filename[i];
               }
               if ( strcmp( p, "*.*" ) == 0 )
               {
                  p = "";
               }
               TextDraw( hdc, static_cast<LONG>(XLEFT*1/8+(i%5)*size.cx/5), static_cast<LONG>((i/5+1)*etm.cySpaced*5/4)-etm.cyAscent, "%c:%s", aMarker[i], p );
            }

            double LX = 0;
            const double LY=YMAX/20+YMAX*i/10;
            double LDIFF = FLT_MAX;

            switch ( TYPE[i][0] )
            {
               case 'i':
               {
                  {
                     {
                        for ( int j = 0; j < ICgraph[i]; ++j )
                        {
                           POINT pt = { static_cast<LONG>(XLEFT+FNISCL(CFM[i][j],XLEFT,XRIGHT,0,XMAX)), static_cast<LONG>(YBOTTOM-FNISCL(fabs(PRESUR[i][j]),YTOP,YBOTTOM,0,YMAX))-etm.cyAscent };
                           TextDrawCentered( hdc, pt.x, pt.y, "%c", aMarker[i] );
                        }
                     }
                  }

                  {
                     if ( bBestFitCurve )
                     {
                        #if 0
                        if ( M[i] <= 0 )
                        {
                           break;
                        }
                        #endif
                        bool bFirstTime = true;
                        {
                           for ( double PX = 0.1; PX <= XMAX; PX += 0.5, bFirstTime = false )
                           {
                              const double PY=A[i]*pow(PX,B[i])+fabs(PRESUR[i][0]);
                              {
                                 POINT pt = { static_cast<LONG>(XLEFT+FNISCL(PX,XLEFT,XRIGHT,0,XMAX)), static_cast<LONG>(YBOTTOM-FNISCL(PY,YTOP,YBOTTOM,0,YMAX)) };

                                 if ( ( pt.x <= XRIGHT ) && ( pt.y >= YTOP ) )
                                 {
                                    if ( bFirstTime )
                                    {
                                       MoveToEx( hdc, pt.x, pt.y, 0 );
                                    }
                                    else
                                    {
                                       LineTo( hdc, pt.x, pt.y );
                                    }
                                 }

                                 {
                                    const double diff = fabs(PY-LY);
                                    if ( diff < LDIFF )
                                    {
                                       LX = PX;
                                       LDIFF = diff;
                                    }
                                 }
                              }
                           }
                        }
                     }
                     else
                     {
                        bool bFirstTime = true;
                        {
                           for ( int j = 0; j < ICgraph[i]; ++j, bFirstTime = false )
                           {
                              const double PX = CFM[i][j];
                              const double PY = fabs(PRESUR[i][j]);
                              {
                                 POINT pt = { static_cast<LONG>(XLEFT+FNISCL(PX,XLEFT,XRIGHT,0,XMAX)), static_cast<LONG>(YBOTTOM-FNISCL(PY,YTOP,YBOTTOM,0,YMAX)) };

                                 if ( ( pt.x <= XRIGHT ) && ( pt.y >= YTOP ) )
                                 {
                                    if ( bFirstTime )
                                    {
                                       MoveToEx( hdc, pt.x, pt.y, 0 );
                                    }
                                    else
                                    {
                                       LineTo( hdc, pt.x, pt.y );
                                    }
                                 }

                                 {
                                    const double diff = fabs(PY-LY);
                                    if ( diff < LDIFF )
                                    {
                                       LX = PX;
                                       LDIFF = diff;
                                    }
                                 }
                              }
                           }
                        }
                     }
                  }

                  break;
               }

               case 'f':
               {
                  {
                     int FirstTime = 1;
                     {
                        for ( int j = 0; j < ICgraph[i]; ++j, FirstTime = 0 )
                        {
                           const double PX = CFM[i][j];
                           const double PY = fabs(PRESUR[i][j]);

                           POINT pt = { static_cast<LONG>(XLEFT+FNISCL(PX,XLEFT,XRIGHT,0,XMAX)), static_cast<LONG>(YBOTTOM-FNISCL(PY,YTOP,YBOTTOM,0,YMAX)) };

                           if ( FirstTime )
                           {
                              MoveToEx( hdc, pt.x, pt.y, 0 );
                           }
                           else
                           {
                              LineTo( hdc, pt.x, pt.y );
                           }

                           {
                              const double diff = fabs(PY-LY);
                              if ( diff < LDIFF )
                              {
                                 LX = PX;
                                 LDIFF = diff;
                              }
                           }

                        }
                     }
                  }

                  break;
               }
            }

            {
               int JX=static_cast<LONG>(XLEFT+FNISCL(LX,XLEFT,XRIGHT,0,XMAX));
               const int JY=static_cast<LONG>(YBOTTOM-FNISCL(LY,YTOP,YBOTTOM,0,YMAX));
               {
                  const bool bAlignRight = (LX>(XMAX/2));
                  if ( bAlignRight )
                  {
                     JX -= 10;
                  }
                  else
                  {
                     JX += 10;
                  }
                  {
                     char buffer[110] = "";
                     if ( ! bAlignRight )
                     {
                        sprintfsafecat( buffer, sizeof(buffer), "<-- " );
                     }
                     sprintfsafecat( buffer, sizeof(buffer), "%.58s", FANORBOX[i] );
                     striptrailblanks( buffer );
                     {
                        switch ( TYPE[i][0] )
                        {
                           case 'f':
                           {
                              if ( ! bIsSystemFan )
                              {
                                 strcatarray( buffer, ", " );
                                 if ( RPM[i] )
                                 {
                                    sprintfsafecat( buffer, sizeof(buffer), "%.0f RPM, ", RPM[i] );
                                 }
                                 if ( PWM[i] >= 0 )
                                 {
                                    sprintfsafecat( buffer, sizeof(buffer), "%.0f%% PWM duty cycle, ", PWM[i] );
                                 }
                                 if ( SMM[i] == -1 )
                                 {
                                    strcatarray( buffer, "Blower" );
                                 }
                                 else
                                 {
                                    sprintfsafecat( buffer, sizeof(buffer), "%.0f mm", SMM[i] );
                                 }
                              }
                              break;
                           }
                        }
                     }
                     if ( bAlignRight )
                     {
                        sprintfsafecat( buffer, sizeof(buffer), " -->" );
                     }
                     void (*const pfn)( HDC, LONG, LONG, const char*, ... ) = bAlignRight ? TextDrawRightAligned : TextDraw;
                     (*pfn)( hdc, JX, JY-etm.cyAscent, "%s", buffer );
                  }
               }
            }

            SetTextColor( hdc, colorOld );
            SelectPen( hdc, hpenOld );
            DeletePen( hpen );
         }
      }
   }

   SelectFont( hdc, hfontOld );
   DeleteFont( hfont );

   Mutex.Release();
}

//-----------------------------------------------------------------

static double CFMTOP;
const double minCFMTOP = 0.1;
const int maxlengthCFMTOP = 5;
const char formatCFMTOP[] = "%.1f";
const double precisionCFMTOP = 0.1;

static double MaximumForCFMTOP()
{
   if ( AbType == ABTYPE_001 )
   {
      return Trunc( min( bb*bb/4/fabs(cc), LL*1.15 ), precisionCFMTOP );
   }
   return 2250;
}

//------------------------------------------------------------------

static void FixPrepareControls( HWND hwnd, char tempTYPE, bool tempIsSystemFan, bool bIgnoreRPM, bool bIgnorePWM )
{
   switch ( tempTYPE )
   {
      case 'i':
      {
         SetDlgItemText( hwnd, ID_TEXT_FANORBOX, "System model or box under test plus description" );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_FANORBOX   ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_EF_FANORBOX     ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_CFMTOP     ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_EDIT_CFMTOP     ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_SPIN_CFMTOP     ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_CHECK_SYSTEMFAN ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_VDC        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_EDIT_VDC        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_SPIN_VDC        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_RPM        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_EDIT_RPM        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_SPIN_RPM        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_CHECK_NORPM     ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_PWM        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_EDIT_PWM        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_SPIN_PWM        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_CHECK_NOPWM     ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_SMM        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_25           ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_40           ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_50           ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_60           ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_70           ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_80           ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_92           ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_120          ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_150          ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_170          ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_BLOWER       ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_PULSETIME  ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_SPIN_PULSETIME  ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_EDIT_PULSETIME  ), true );
         break;
      }
      case 'r':
      {
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_FANORBOX   ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_EF_FANORBOX     ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_CFMTOP     ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_EDIT_CFMTOP     ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_SPIN_CFMTOP     ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_CHECK_SYSTEMFAN ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_VDC        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_EDIT_VDC        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_SPIN_VDC        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_RPM        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_EDIT_RPM        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_SPIN_RPM        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_CHECK_NORPM     ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_PWM        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_EDIT_PWM        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_SPIN_PWM        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_CHECK_NOPWM     ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_SMM        ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_25           ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_40           ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_50           ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_60           ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_70           ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_80           ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_92           ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_120          ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_150          ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_170          ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_BLOWER       ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_PULSETIME  ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_SPIN_PULSETIME  ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_EDIT_PULSETIME  ), false );
         break;
      }
      case 'f':
      {
         SetDlgItemText( hwnd, ID_TEXT_FANORBOX, "Manufacturer's identification number plus description" );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_FANORBOX   ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_EF_FANORBOX     ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_CFMTOP     ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_EDIT_CFMTOP     ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_SPIN_CFMTOP     ), false );
         ShowHideWindow( GetDlgItem( hwnd, ID_CHECK_SYSTEMFAN ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_VDC        ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_EDIT_VDC        ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_SPIN_VDC        ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_RPM        ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_EDIT_RPM        ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_SPIN_RPM        ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_CHECK_NORPM     ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_PWM        ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_EDIT_PWM        ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_SPIN_PWM        ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_CHECK_NOPWM     ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_SMM        ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_25           ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_40           ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_50           ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_60           ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_70           ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_80           ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_92           ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_120          ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_150          ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_170          ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_RB_BLOWER       ), true );
         EnableDisableWindow( GetDlgItem( hwnd, ID_TEXT_VDC )    , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_EDIT_VDC )    , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_SPIN_VDC )    , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_TEXT_RPM )    , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_EDIT_RPM )    , !tempIsSystemFan && !bIgnoreRPM );
         EnableDisableWindow( GetDlgItem( hwnd, ID_SPIN_RPM )    , !tempIsSystemFan && !bIgnoreRPM );
         EnableDisableWindow( GetDlgItem( hwnd, ID_CHECK_NORPM ) , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_TEXT_PWM )    , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_EDIT_PWM )    , !tempIsSystemFan && !bIgnorePWM );
         EnableDisableWindow( GetDlgItem( hwnd, ID_SPIN_PWM )    , !tempIsSystemFan && !bIgnorePWM );
         EnableDisableWindow( GetDlgItem( hwnd, ID_CHECK_NOPWM ) , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_TEXT_SMM )    , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_RB_25 )       , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_RB_40 )       , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_RB_50 )       , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_RB_60 )       , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_RB_70 )       , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_RB_80 )       , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_RB_92 )       , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_RB_120 )      , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_RB_150 )      , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_RB_170 )      , !tempIsSystemFan                );
         EnableDisableWindow( GetDlgItem( hwnd, ID_RB_BLOWER )   , !tempIsSystemFan                );
         ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_PULSETIME  ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_SPIN_PULSETIME  ), true );
         ShowHideWindow( GetDlgItem( hwnd, ID_EDIT_PULSETIME  ), true );
         break;
      }
   }
}

static INT_PTR CALLBACK PrepareDlgProc( HWND hwnd, UINT message, WPARAM wParam, LPARAM lParam )
{
   static char tempTYPE;
   static double tempSMM;
   static double tempPulseTimeInterval;
   static bool bIgnoreRPM;
   static bool bIgnorePWM;
   static bool tempIsSystemFan;

   switch ( message )
   {
      case WM_INITDIALOG:
      {
         CenterWindow( hwnd );
         EnableDisableMenuItem( GetSystemMenu(hwnd,FALSE), SC_CLOSE, false );

         const int i = 0;

         tempTYPE = TYPE[i][0];

         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EF_FANORBOX );
            winassert( hwndEdit );

            SubclassFieldInvalidChars( hwndEdit, "\"" );

            Edit_LimitText( hwndEdit, sizeof(FANORBOX[i])-1 );

            SetWindowText( hwndEdit, FANORBOX[i] );
         }

         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFMTOP );
            winassert( hwndEdit );

            SubclassFieldReal( hwndEdit, formatCFMTOP, precisionCFMTOP, minCFMTOP, MaximumForCFMTOP() );

            Edit_LimitText( hwndEdit, maxlengthCFMTOP );

            SetWindowTextf( hwndEdit, formatCFMTOP, static_cast<double>(minCFMTOP) );
         }

         tempIsSystemFan = bIsSystemFan;
         {
            CheckUncheckButton( hwnd, ID_CHECK_SYSTEMFAN, tempIsSystemFan );
         }

         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_VDC );
            winassert( hwndEdit );

            SubclassFieldReal( hwndEdit, formatVDC, precisionVDC, minVDC, maxVDC );

            Edit_LimitText( hwndEdit, maxlengthVDC );

            SetWindowTextf( hwndEdit, formatVDC, VDC[i] );
         }

         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_RPM );
            winassert( hwndEdit );

            SubclassFieldUnsigned( hwndEdit, formatRPM, minRPM, maxRPM, incrementRPM );

            Edit_LimitText( hwndEdit, maxlengthRPM );

            SetWindowTextf( hwndEdit, formatRPM, static_cast<int>(max(RPM[i],minRPM)) );
         }
         bIgnoreRPM = !RPM[i];
         {
            CheckUncheckButton( hwnd, ID_CHECK_NORPM, bIgnoreRPM );
         }

         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_PWM );
            winassert( hwndEdit );

            SubclassFieldUnsigned( hwndEdit, formatPWM, minPWM, maxPWM, incrementPWM );

            Edit_LimitText( hwndEdit, maxlengthPWM );

            SetWindowTextf( hwndEdit, formatPWM, static_cast<int>(max(PWM[i],minPWM)) );
         }
         bIgnorePWM = PWM[i] < 0;
         {
            CheckUncheckButton( hwnd, ID_CHECK_NOPWM, bIgnorePWM );
         }

         tempPulseTimeInterval = PulseTimeInterval[i];

         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_PULSETIME );
            winassert( hwndEdit );

            SubclassFieldReal( hwndEdit, formatPULSETIME, precisionPULSETIME, minPULSETIME, maxPULSETIME );

            Edit_LimitText( hwndEdit, maxlengthPULSETIME );

            switch ( tempTYPE )
            {
               case 'i':
               case 'f':
               {
                  SetWindowTextf( hwndEdit, formatPULSETIME, tempPulseTimeInterval );
                  break;
               }
               case 'r':
               {
                  SetWindowText( hwndEdit, "" );
               }
            }
         }

         tempSMM = SMM[i];

         {
            int id = 0;
            {
               switch ( static_cast<int>(tempSMM) )
               {
                  case 25:
                  {
                     id = ID_RB_25;
                     break;
                  }
                  case 40:
                  {
                     id = ID_RB_40;
                     break;
                  }
                  case 50:
                  {
                     id = ID_RB_50;
                     break;
                  }
                  case 60:
                  {
                     id = ID_RB_60;
                     break;
                  }
                  case 70:
                  {
                     id = ID_RB_70;
                     break;
                  }
                  case 80:
                  {
                     id = ID_RB_80;
                     break;
                  }
                  case 92:
                  {
                     id = ID_RB_92;
                     break;
                  }
                  case 120:
                  {
                     id = ID_RB_120;
                     break;
                  }
                  case 150:
                  {
                     id = ID_RB_150;
                     break;
                  }
                  case 170:
                  {
                     id = ID_RB_170;
                     break;
                  }
                  case -1:
                  {
                     id = ID_RB_BLOWER;
                     break;
                  }
                  default:
                  {
                     tempSMM = 25;
                     id = ID_RB_25;
                     break;
                  }
               }
            }

            CheckUncheckButton( hwnd, id, true );
         }

         {
            int id = 0;
            {
               switch ( tempTYPE )
               {
                  case 'i':
                  {
                     id = ID_RADIO_IMPEDANCE;
                     break;
                  }
                  case 'r':
                  {
                     id = ID_RADIO_FLOWRATE;
                     break;
                  }
                  case 'f':
                  {
                     id = ID_RADIO_FAN;
                     break;
                  }
               }
            }

            CheckUncheckButton( hwnd, id, true );

         }

         FixPrepareControls( hwnd, tempTYPE, tempIsSystemFan, bIgnoreRPM, bIgnorePWM );
         return TRUE;
      }

      case WM_NOTIFY:
      {
         const int id = wParam;
         const NMHDR*const pnmhdr = reinterpret_cast<NMHDR*>(lParam);

         switch ( id )
         {
            case ID_SPIN_CFMTOP:
            {
               switch ( pnmhdr->code )
               {
                  case UDN_DELTAPOS:
                  {
                     const NMUPDOWN* pUpDown = reinterpret_cast<NMUPDOWN*>(lParam);
                     const int iDelta = pUpDown->iDelta;
                     if ( iDelta < 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFMTOP, WM_KEYDOWN, VK_UP, 0 );
                     }
                     else if ( iDelta > 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFMTOP, WM_KEYDOWN, VK_DOWN, 0 );
                     }
                     break;
                  }
               }
               break;
            }

            case ID_SPIN_VDC:
            {
               switch ( pnmhdr->code )
               {
                  case UDN_DELTAPOS:
                  {
                     const NMUPDOWN* pUpDown = reinterpret_cast<NMUPDOWN*>(lParam);
                     const int iDelta = pUpDown->iDelta;
                     if ( iDelta < 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_VDC, WM_KEYDOWN, VK_UP, 0 );
                     }
                     else if ( iDelta > 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_VDC, WM_KEYDOWN, VK_DOWN, 0 );
                     }
                     break;
                  }
               }
               break;
            }

            case ID_SPIN_RPM:
            {
               switch ( pnmhdr->code )
               {
                  case UDN_DELTAPOS:
                  {
                     const NMUPDOWN* pUpDown = reinterpret_cast<NMUPDOWN*>(lParam);
                     const int iDelta = pUpDown->iDelta;
                     if ( iDelta < 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_RPM, WM_KEYDOWN, VK_UP, 0 );
                     }
                     else if ( iDelta > 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_RPM, WM_KEYDOWN, VK_DOWN, 0 );
                     }
                     break;
                  }
               }
               break;
            }

            case ID_SPIN_PWM:
            {
               switch ( pnmhdr->code )
               {
                  case UDN_DELTAPOS:
                  {
                     const NMUPDOWN* pUpDown = reinterpret_cast<NMUPDOWN*>(lParam);
                     const int iDelta = pUpDown->iDelta;
                     if ( iDelta < 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_PWM, WM_KEYDOWN, VK_UP, 0 );
                     }
                     else if ( iDelta > 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_PWM, WM_KEYDOWN, VK_DOWN, 0 );
                     }
                     break;
                  }
               }
               break;
            }

            case ID_SPIN_PULSETIME:
            {
               switch ( pnmhdr->code )
               {
                  case UDN_DELTAPOS:
                  {
                     const NMUPDOWN* pUpDown = reinterpret_cast<NMUPDOWN*>(lParam);
                     const int iDelta = pUpDown->iDelta;
                     if ( iDelta < 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_PULSETIME, WM_KEYDOWN, VK_UP, 0 );
                     }
                     else if ( iDelta > 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_PULSETIME, WM_KEYDOWN, VK_DOWN, 0 );
                     }
                     break;
                  }
               }
               break;
            }

         }
         break;
      }

      case WM_COMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         const WORD wCode = HIWORD(wParam);

         const int i = 0;

         switch ( wCmd )
         {
            case IDOK:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     {
                        switch ( tempTYPE )
                        {
                           case 'i':
                           case 'f':
                           {
                              const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_PULSETIME );
                              winassert( hwndEdit );

                              char buffer[80+1] = "";
                              GetWindowText( hwndEdit, buffer, sizeof(buffer) );
                              tempPulseTimeInterval = StringToFloat( buffer, precisionPULSETIME, minPULSETIME, maxPULSETIME );

                              if ( ! IsValid(tempPulseTimeInterval) )
                              {
                                 SetFocus( hwndEdit );
                                 BeepError();
                                 return TRUE;
                              }

                              break;
                           }
                           case 'r':
                           {
                              tempPulseTimeInterval = DefaultPulseTimeInterval( tempTYPE );
                              break;
                           }
                        }
                     }

                     {
                        switch ( tempTYPE )
                        {
                           case 'i':
                           {
                              double tempCFMTOP = CFMTOP;
                              {
                                 const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFMTOP );
                                 winassert( hwndEdit );

                                 char buffer[80+1] = "";
                                 GetWindowText( hwndEdit, buffer, sizeof(buffer) );
                                 tempCFMTOP = StringToFloat( buffer, precisionCFMTOP, minCFMTOP, MaximumForCFMTOP() );
                                 if ( ! IsValid(tempCFMTOP) )
                                 {
                                    BeepError();
                                 }
                                 else
                                 {
                                    if ( AbType == ABTYPE_001 )
                                    {
                                       char message[1024] = "";
                                       bool bTerminate = false;
                                       if ( tempCFMTOP > LL )
                                       {
                                          strcpyarray( message,
                                             "Calibrated limits will be exceeded and errors may occur."
                                             "\n\nAre you sure you want to continue?"
                                          );
                                       }
                                       else if ( tempCFMTOP/LL*8 > pp )
                                       {
                                          strcpyarray( message,
                                             "Manometer maximum pressure would be exceeded."
                                             "\n\nTest cannot be permitted."
                                          );
                                          bTerminate = true;
                                       }
                                       if ( *message )
                                       {
                                          if ( bTerminate )
                                          {
                                             MsgOkError( "ERROR!", message );
                                             tempCFMTOP = BADFLOAT;
                                          }
                                          else
                                          {
                                             if ( ! MsgIsYes( MsgYesNoWarning( "WARNING!", message ) ) )
                                             {
                                                tempCFMTOP = BADFLOAT;
                                             }
                                          }
                                       }
                                    }
                                 }
                                 if ( ! IsValid(tempCFMTOP) )
                                 {
                                    SetFocus( hwndEdit );
                                    return TRUE;
                                 }
                              }

                              {
                                 HE[i][0] = '\0';
                                 HE[i][1] = '\0';
                                 ACDC[i][0] = '\0';
                                 ACDC[i][1] = '\0';
                              }

                              {
                                 CFMTOP = tempCFMTOP;
                              }

                              {
                                 VDC[i] = 0;                      // only used for FAN
                                 RPM[i] = 0;                      // only used for FAN
                                 SMM[i] = 0;                      // only used for FAN
                                 PWM[i] = 0;                      // only used for FAN
                              }

                              break;
                           }

                           case 'r':
                           {
                              {
                                 HE[i][0] = '\0';
                                 HE[i][1] = '\0';
                                 ACDC[i][0] = '\0';
                                 ACDC[i][1] = '\0';
                              }

                              {
                                 CFMTOP = 0;
                              }

                              {
                                 VDC[i] = 0;                      // only used for FAN
                                 RPM[i] = 0;                      // only used for FAN
                                 SMM[i] = 0;                      // only used for FAN
                                 PWM[i] = 0;                      // only used for FAN
                              }

                              break;
                           }

                           case 'f':
                           {
                              double tempVDC = VDC[i];
                              {
                                 const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_VDC );
                                 winassert( hwndEdit );

                                 char buffer[80+1] = "";
                                 GetWindowText( hwndEdit, buffer, sizeof(buffer) );
                                 tempVDC = StringToFloat( buffer, precisionVDC, minVDC, maxVDC );

                                 if ( ! IsValid(tempVDC) )
                                 {
                                    SetFocus( hwndEdit );
                                    BeepError();
                                    return TRUE;
                                 }
                              }

                              double tempRPM = RPM[i];
                              if ( bIgnoreRPM )
                              {
                                 tempRPM = 0;
                              }
                              else
                              {
                                 const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_RPM );
                                 winassert( hwndEdit );

                                 char buffer[80+1] = "";
                                 GetWindowText( hwndEdit, buffer, sizeof(buffer) );
                                 const int value = StringToInt( buffer, minRPM, maxRPM );

                                 if ( ! IsValid(value) )
                                 {
                                    SetFocus( hwndEdit );
                                    BeepError();
                                    return TRUE;
                                 }

                                 tempRPM = static_cast<double>(value);
                              }

                              double tempPWM = PWM[i];
                              if ( bIgnorePWM )
                              {
                                 tempPWM = -1;
                              }
                              else
                              {
                                 const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_PWM );
                                 winassert( hwndEdit );

                                 char buffer[80+1] = "";
                                 GetWindowText( hwndEdit, buffer, sizeof(buffer) );
                                 const int value = StringToInt( buffer, minPWM, maxPWM );

                                 if ( ! IsValid(value) )
                                 {
                                    SetFocus( hwndEdit );
                                    BeepError();
                                    return TRUE;
                                 }

                                 tempPWM = static_cast<double>(value);
                              }

                              {
                                 HE[i][0] = 'N';                     // set HE = N
                                 HE[i][1] = '\0';
                                 ACDC[i][0] = 'D';                   // set ACDC = D for DC voltage
                                 ACDC[i][1] = '\0';
                              }

                              {
                                 CFMTOP = 0;
                              }

                              {
                                 VDC[i] = tempVDC;
                                 RPM[i] = tempRPM;
                                 SMM[i] = tempSMM;
                                 PWM[i] = tempPWM;
                              }

                              break;
                           }
                        }
                     }

                     PulseTimeInterval[i] = tempPulseTimeInterval;

                     bIsSystemFan = tempIsSystemFan;

                     TYPE[i][0] = tempTYPE;
                     TYPE[i][1] = '\0';

                     {
                        GetDlgItemText( hwnd, ID_EF_FANORBOX, FANORBOX[i], sizeof(FANORBOX[i]) );

                        {
                           for ( char* p = FANORBOX[i]; *p; ++p )
                           {
                              if ( *p == '"' )
                              {
                                 *p = '\'';
                              }
                           }
                        }
                     }

                     EndDialog( hwnd, wCmd );
                     return TRUE;
                  }
               }
               return FALSE;
            }

            case IDCANCEL:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     EndDialog( hwnd, wCmd );
                     return TRUE;
                  }
               }
               return FALSE;
            }

            case ID_RADIO_IMPEDANCE:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     tempTYPE = 'i';
                     FixPrepareControls( hwnd, tempTYPE, tempIsSystemFan, bIgnoreRPM, bIgnorePWM );
                     {
                        tempPulseTimeInterval = DefaultPulseTimeInterval( tempTYPE );
                        SetDlgItemTextf( hwnd, ID_EDIT_PULSETIME, formatPULSETIME, tempPulseTimeInterval );
                     }
                     break;
                  }
               }
               break;
            }

            case ID_RADIO_FLOWRATE:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     tempTYPE = 'r';
                     FixPrepareControls( hwnd, tempTYPE, tempIsSystemFan, bIgnoreRPM, bIgnorePWM );
                     {
                        tempPulseTimeInterval = DefaultPulseTimeInterval( tempTYPE );
                        SetDlgItemText( hwnd, ID_EDIT_PULSETIME, "" );
                     }
                     break;
                  }
               }
               break;
            }

            case ID_RADIO_FAN:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     tempTYPE = 'f';
                     FixPrepareControls( hwnd, tempTYPE, tempIsSystemFan, bIgnoreRPM, bIgnorePWM );
                     {
                        tempPulseTimeInterval = DefaultPulseTimeInterval( tempTYPE );
                        SetDlgItemTextf( hwnd, ID_EDIT_PULSETIME, formatPULSETIME, tempPulseTimeInterval );
                     }
                     break;
                  }
               }
               break;
            }

            case ID_CHECK_SYSTEMFAN:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     tempIsSystemFan = ! tempIsSystemFan;
                     CheckUncheckButton( hwnd, wCmd, tempIsSystemFan );
                     FixPrepareControls( hwnd, tempTYPE, tempIsSystemFan, bIgnoreRPM, bIgnorePWM );
                     return 0;
                  }
               }
               return 0;
            }

            case ID_RB_25:
            case ID_RB_40:
            case ID_RB_50:
            case ID_RB_60:
            case ID_RB_70:
            case ID_RB_80:
            case ID_RB_92:
            case ID_RB_120:
            case ID_RB_150:
            case ID_RB_170:
            case ID_RB_BLOWER:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     LONG value = 0;

                     switch ( wCmd )
                     {
                        case ID_RB_25:
                        {
                           value = 25;
                           break;
                        }
                        case ID_RB_40:
                        {
                           value = 40;
                           break;
                        }
                        case ID_RB_50:
                        {
                           value = 50;
                           break;
                        }
                        case ID_RB_60:
                        {
                           value = 60;
                           break;
                        }
                        case ID_RB_70:
                        {
                           value = 70;
                           break;
                        }
                        case ID_RB_80:
                        {
                           value = 80;
                           break;
                        }
                        case ID_RB_92:
                        {
                           value = 92;
                           break;
                        }
                        case ID_RB_120:
                        {
                           value = 120;
                           break;
                        }
                        case ID_RB_150:
                        {
                           value = 150;
                           break;
                        }
                        case ID_RB_170:
                        {
                           value = 170;
                           break;
                        }
                        case ID_RB_BLOWER:
                        {
                           value = -1;
                           break;
                        }
                     }
                     assert( (value>0) || (value==-1) );

                     tempSMM = static_cast<double>(value);

                     break;
                  }
               }

               break;
            }

            case ID_CHECK_NORPM:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     bIgnoreRPM = ! bIgnoreRPM;
                     CheckUncheckButton( hwnd, wCmd, bIgnoreRPM );
                     FixPrepareControls( hwnd, tempTYPE, tempIsSystemFan, bIgnoreRPM, bIgnorePWM );
                     if ( ! bIgnoreRPM )
                     {
                        SetFocus( GetDlgItem( hwnd, ID_EDIT_RPM ) );
                     }
                     return 0;
                  }
               }
               return 0;
            }

            case ID_CHECK_NOPWM:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     bIgnorePWM = ! bIgnorePWM;
                     CheckUncheckButton( hwnd, wCmd, bIgnorePWM );
                     FixPrepareControls( hwnd, tempTYPE, tempIsSystemFan, bIgnoreRPM, bIgnorePWM );
                     if ( ! bIgnorePWM )
                     {
                        SetFocus( GetDlgItem( hwnd, ID_EDIT_PWM ) );
                     }
                     return 0;
                  }
               }
               return 0;
            }

         }

         return FALSE;
      }

      case WM_SYSCOMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         switch (wCmd)
         {
            case SC_CLOSE:
            {
               return TRUE;
            }
         }
         return FALSE;
      }
   }

   return FALSE;
}

static bool Prepare( HWND hwndParent )
{
   const INT_PTR rc = DialogBoxParam( hinst, MAKEINTRESOURCE(ID_DLG_PREPARE), hwndParent, PrepareDlgProc, 0 );
   winassert( rc > 0 );
   return ( rc == IDOK );
}

//--------------------------------------------------------------------

static HDC hdcAutoPrint = 0;

//--------------------------------------------------------------------

namespace
{
   struct RunThreadStruct
   {
      HWND hwndDlg;
   };
}

static KillerClass RunKiller;

static void RunUpdateStatus( const RunThreadStruct* psThread, const char* fmt, ... )
{
   if ( ! psThread )
   {
      return;
   }

   const int buffersize = 1024;
   char buffer[buffersize] = "";

   char* psz1 = 0;
   char* psz2 = 0;

   {
      if ( fmt != NULL )
      {
         {
            va_list arg_ptr;
            va_start( arg_ptr, fmt );
            vsprintfsafe( buffer, sizeof(buffer), fmt, arg_ptr );
            va_end( arg_ptr );
         }
         psz1 = buffer;
      }
   }

   {
      if ( psz1 )
      {
         char* p = strchr( psz1, '\n' );
         if ( p )
         {
            if ( p == psz1 )
            {
               psz1 = 0;
            }
            *p = '\0';
            ++p;
            psz2 = p;
         }
      }
   }

   RunKiller.Check();

   SendMessage( psThread->hwndDlg, WM_USER_RUN_UPDATE_STATUS, WPARAM(psz1), LPARAM(psz2) );
}

//--------------------------------------------------------------------

#define DEFAULTGPIBADDR 10
static int gpibaddr = DEFAULTGPIBADDR;

static void Reset()
{
   gpib.ibwrt( gpibaddr, -1, "*RST" );
}

static void BeginOpeningValve()
{
   gpib.ibwrt( gpibaddr, -1, "SOUR:VOLT 12.0, (@205)" );
}

static void BeginClosingValve()
{
   gpib.ibwrt( gpibaddr, -1, "SOUR:VOLT 12.0, (@204)" );
}

//--------------------------------------------------------------------

static const char*const aPorts[] =
{
   "",
   "COM1",
   "COM2",
   "COM3",
   "COM4",
   "COM5",
   "COM6",
   "COM7",
   "COM8",
   "COM9",
};

#define BADHANDLE -1

#define nullport 0

class SerialException
{

public:

   explicit SerialException( const char* inInfo )
   {
      strcpyarray( szInfo, inInfo );
   }

   const char* Info() const
   {
      return szInfo;
   }

private:

   explicit SerialException();
   SerialException& operator=(const SerialException&);

   char szInfo[80];

};

int SetupSerialPort( const char filespec[] )
{
   if ( ! NOINIT )
   {
      HANDLE hComm = CreateFile(
                                 filespec,
                                 GENERIC_READ|GENERIC_WRITE,
                                 0,
                                 NULL,
                                 OPEN_EXISTING,
                                 FILE_ATTRIBUTE_NORMAL|FILE_FLAG_OVERLAPPED,
                                 NULL
      );
      if ( hComm == INVALID_HANDLE_VALUE )
      {
         MsgOk( "Can't run test!", "Could not setup serial port '%s' (rc=%d) !\n", filespec, GetLastError() );
         return BADHANDLE;
      }
      SetupComm( hComm, 4096, 4096 );
      {
         COMMTIMEOUTS CommTimeOuts;
         {
            CommTimeOuts.ReadIntervalTimeout = MAXDWORD;
            CommTimeOuts.ReadTotalTimeoutMultiplier = 0 ;
            CommTimeOuts.ReadTotalTimeoutConstant = 1000 ;
            CommTimeOuts.WriteTotalTimeoutMultiplier = 2;
            CommTimeOuts.WriteTotalTimeoutConstant = 0 ;
         }
         SetCommTimeouts(hComm, &CommTimeOuts);
      }
      {
         DCB dcb = { 0 };
         GetCommState( hComm, &dcb );
         {
            dcb.BaudRate=CBR_9600;
            dcb.ByteSize=8;
            dcb.Parity=NOPARITY;
            dcb.fParity=FALSE;
            dcb.StopBits=ONESTOPBIT;
            dcb.fRtsControl=RTS_CONTROL_DISABLE;
            dcb.fDtrControl=DTR_CONTROL_DISABLE;
            dcb.fDsrSensitivity=FALSE;
            dcb.fOutxCtsFlow=FALSE;
            dcb.fOutxDsrFlow=FALSE;
            dcb.fOutX=FALSE;
            dcb.fInX=FALSE;
         }
         SetCommState( hComm, &dcb );
      }
      CloseHandle(hComm);
   }
   int handle = _open( filespec, _O_BINARY | _O_RDWR, _S_IREAD | _S_IWRITE );
   if ( handle == BADHANDLE )
   {
      MsgOk( "Can't run test!", "Could not open serial port '%s' (rc=%d) !\n", filespec, errno );
      return BADHANDLE;
   }
   return handle;
}

void CloseSerialPort( int& handle )
{
   if ( handle != BADHANDLE )
   {
      _close( handle ), handle = BADHANDLE;
   }
}

char* GetSerialData( int handle, const char* string, const char* tag, char* buf, int cbbuf )
{
   for ( int t = 0; t < 5; ++t )
   {
      memset( buf, 0, cbbuf );
      Sleep( 500 );
      {
         char info[80] = "";
         strcpyarray( info, string );
         striptrailblanks( info );
         printf( "(Writing '%s' to serial port...)\n", info );
      }
      const int cbwrite =  _write( handle, string, strlen(string) );
      if ( cbwrite < 0 )
      {
         printf( "ERROR!  Could not write to serial port (rc=%d) !\n", errno );
         abort();
      }
      if ( cbwrite != static_cast<int>(strlen(string)) )
      {
         printf( "ERROR!  Only %d bytes written to serial port !\n", cbwrite );
         abort();
      }
      Sleep( 1500 );
      {
         printf( "(Reading from serial port...)\n" );
      }
      const int cbread = _read( handle, buf, cbbuf );
      if ( cbread < 0 )
      {
         printf( "ERROR!  Could not read from serial port (rc=%d) !\n", errno );
         abort();
      }
      buf[cbread] = '\0';
      if ( strnicmp( buf, tag, strlen(tag) ) == 0 )
      {
         return buf + strlen(tag);
      }
      {
         for ( int r = 0; r < cbread; ++r )
         {
            if ( isspace(r) && ( buf[r] != ' ' ) )
            {
               buf[r] = '.';
            }
         }
      }
      printf( "ERROR!  Invalid response '%s' !\n", buf );
      Sleep( 1500 );
   }
   throw SerialException( "Invalid response from serial port" );
}

void DoSerialCommand( int handle, const char* string, const char* tag )
{
   char buffer[80];
   GetSerialData( handle, string, tag, buffer, sizeof(buffer) );
}

double GetSerialFloat( int handle, const char* string, const char* tag )
{
   char buffer[80];
   char* p = GetSerialData( handle, string, tag, buffer, sizeof(buffer) );
   return atof( p );
}

static int handlePressure = BADHANDLE;
static int handleCFM = BADHANDLE;

static int portPressure = nullport;
static int portCFM = nullport;

//--------------------------------------------------------------------

static double ReadStaticPressure()
{
   char string[_MAX_PATH] = "";
   gpib.ibwrt( gpibaddr, -1, "MEASure:VOLTage:DC? (@101)" );
   Sleep( 250 );
   gpib.ibrd( gpibaddr, -1, string, sizeof(string) );
   const double d = atof( string );
   return d;
}

static double ReadDynamicPressure()
{
   char string[_MAX_PATH] = "";
   gpib.ibwrt( gpibaddr, -1, "MEASure:VOLTage:DC? (@102)" );
   Sleep( 250 );
   gpib.ibrd( gpibaddr, -1, string, sizeof(string) );
   const double d = atof( string );
   return d;
}

//--------------------------------------------------------------------

static double GetPressure()
{
   if ( DEMO )
   {
      Sleep( 250 );
      #if NEVER
      {
         static int i = 0;
         if ( i++ >= 6 )
         {
            return 4.5;
         }
      }
      #endif
      return 1.0 * ( rand() % 100 ) / 100;
   }
   if ( AbType == ABTYPE_001 )
   {
      return CalcPressure( ReadStaticPressure() );
   }
   printf( "(Reading static pressure from %s...)\n", aPorts[portPressure]) ;
   DoSerialCommand( handlePressure, "@0100\r", "" );
   return GetSerialFloat( handlePressure, "@020?\r", "@020 " );
}

static double GetCFM()
{
   if ( DEMO )
   {
      Sleep( 250 );
      return 1.0 * ( rand() % 100 ) / 100;
   }
   if ( AbType == ABTYPE_001 )
   {
      return CalcCFM( ReadDynamicPressure() );
   }
   printf( "(Reading CFM from %s...)\n", aPorts[portCFM]) ;
   return GetSerialFloat( handleCFM, "d01v0002\r", "d01v0002\r" );
}

//--------------------------------------------------------------------

static int NumPressureSamples()
{
   if ( AbType == ABTYPE_001 )
   {
      return 20;
   }
   return 3;
}

static int NumCFMSamples()
{
   if ( AbType == ABTYPE_001 )
   {
      return 20;
   }
   return 10;
}

static double GetAverageSub( const RunThreadStruct* psThread, int numsamples, double (*pfn)(), const char* label )
{
   if ( numsamples == 1 )
   {
      RunUpdateStatus( psThread, "Collecting %s sample...", label );
      const double d = (*pfn)();
      RunUpdateStatus( psThread, "\nCollected %s sample: %.4f", label, d );
      return d;
   }
   assert( numsamples > 0 );
   RunUpdateStatus( psThread, "Collecting %d %s samples...", numsamples, label );
   double sum = 0;
   {
      for ( int k = 0; k < numsamples; ++k )
      {
         const double d = (*pfn)();
         RunUpdateStatus( psThread, "\nCollected %s sample %d: %.4f", label, k+1, d );
         sum += d;
      }
   }
   return sum / numsamples;
}

static double GetAveragePressure( const RunThreadStruct* psThread )
{
   return GetAverageSub( psThread, NumPressureSamples(), GetPressure, "static pressure" );
}

static double GetAverageCFM( const RunThreadStruct* psThread )
{
   if ( DEMO )
   {
      static int zeros = 4;
      if ( zeros > 0 )
      {
         --zeros;
         return 0;
      }
   }
   return GetAverageSub( psThread, NumCFMSamples(), GetCFM, "CFM" );
}

static void PulseValveOpen( const RunThreadStruct* psThread )
{
   const int i = 0;
   Beep( 2000, 50 );
   const clock_t timeout  = clock() + static_cast<clock_t>(PulseTimeInterval[i]*1000);
   RunUpdateStatus( psThread, "\nBegan opening valve..." );
   BeginOpeningValve();
   Sleep( whole(timeout-clock()) );
   RunUpdateStatus( psThread, "\nStopped opening valve..." );
   Reset();
   Beep( 200, 50 );
}

//--------------------------------------------------------------------

static int gpibaddrpower = 0;

static double getVoltage()
{
   const double d = gpib.ibwrtrdfloataftertagwithdelay( gpibaddrpower, -1, "VOUT", POWER_READ_DELAY, "VOUT?" );
   gpib.ibwrt( gpibaddrpower, -1, "ERR?" ); // to clear dumb error light
   return d;
}

static double getCurrent()
{
   const double d = gpib.ibwrtrdfloataftertagwithdelay( gpibaddrpower, -1, "IOUT", POWER_READ_DELAY, "IOUT?" );
   gpib.ibwrt( gpibaddrpower, -1, "ERR?" ); // to clear dumb error light
   return d;
}

//--------------------------------------------------------------------

class DangerException
{

public:

   explicit DangerException( const char* inInfo )
   {
      strcpyarray( szInfo, inInfo );
   }

   const char* Info() const
   {
      return szInfo;
   }

private:

   explicit DangerException();
   DangerException& operator=(const DangerException&);

   char szInfo[80];

};

static bool bWaiting = false;

static void THREADFUNC RunThread( void* arg )
{
   RunThreadStruct *psThread = static_cast<RunThreadStruct*> ( arg );

   const int i = 0;

   try
   {
      {
         {
            RunUpdateStatus( psThread, "\nVerifying read of CFM...DON'T GO AWAY!!!" );
            GetCFM();
            if ( DEMO )
            {
               Sleep( 250 );
            }
            RunUpdateStatus( psThread, "" );
         }
         {
            RunUpdateStatus( psThread, "\nVerifying read of pressure...DON'T GO AWAY!!!" );
            GetPressure();
            if ( DEMO )
            {
               Sleep( 250 );
            }
            RunUpdateStatus( psThread, "" );
         }
      }

      {
         {
            RunUpdateStatus( psThread, "Make sure static pressure levers are in the correct positions.\nThen press 'Ok' to continue." );
            bWaiting = true;
            RunKiller.Pause();
            SendMessage( psThread->hwndDlg, WM_USER_RUN_OKON, 0, 0 );
            RunKiller.Check();
            SendMessage( psThread->hwndDlg, WM_USER_RUN_OKOFF, 0, 0 );
            RunUpdateStatus( psThread, "" );
         }
      }

      Reset();
      {
         int totalseconds = VALVE_DELAY_SECONDS;
         if ( DEMO )
         {
            #if NEVER
            totalseconds = 10;
            #else
            totalseconds = 2;
            #endif
         }
         int seconds = totalseconds;
         RunUpdateStatus( psThread, "\nBegan opening valve ...DON'T GO AWAY!!!" );
         BeginOpeningValve();
         {
            for ( TimerSeconds timer( seconds ); seconds > 0; seconds = timer.Wait() )
            {
               RunUpdateStatus( psThread, "\nOpening valve for %d more seconds ...DON'T GO AWAY!!!", seconds );
#if KEVIN_CASH
               switch ( TYPE[i][0] )
               {
                  case 'f':
                  {
                     if ( GetPressure() >= PRESSURE_LIMIT )
                     {
                        Reset();
                        BeginClosingValve();
                        char message[80] = "";
                        sprintfsafe( message, sizeof(message), "ERROR!  Static pressure limit of %g has been exceeded!", PRESSURE_LIMIT );
                        RunUpdateStatus( psThread, "%s\nClosing valve ...then test will be terminated!!!", message );
                        seconds = totalseconds - seconds + 2;
                        {
                           for ( TimerSeconds timer( seconds ); seconds > 0; seconds = timer.Wait() )
                           {
                              RunUpdateStatus( psThread, "\nClosing valve for %d more seconds ...then test will be terminated!!!", seconds );
                           }
                        }
                        RunUpdateStatus( psThread, "\nStopped closing valve ...test will be terminated!!!" );
                        Reset();
                        if ( ! DEMO )
                        {
                           throw DangerException( message );
                        }
                     }
                     break;
                  }
               }
#endif
            }
         }
         RunUpdateStatus( psThread, "\nStopped opening valve ...DON'T GO AWAY!!!" );
         Reset();
      }

      {
         char devices[80] = "";
         char verb[80] = "";
         {
            switch ( TYPE[i][0] )
            {
               case 'i':
               case 'r':
               {
                  strcpyarray( devices, "blower" );
                  strcpyarray( verb, "is" );
                  break;
               }
               case 'f':
               {
                  strcpyarray( devices, "blower and fan" );
                  strcpyarray( verb, "are" );
                  break;
               }
            }
         }
         {
            RunUpdateStatus( psThread, "Make sure %s %s off and check for zero on the manometers.\nThen press 'Ok' to continue.", devices, verb );
            bWaiting = true;
            RunKiller.Pause();
            SendMessage( psThread->hwndDlg, WM_USER_RUN_OKON, 0, 0 );
            RunKiller.Check();
            SendMessage( psThread->hwndDlg, WM_USER_RUN_OKOFF, 0, 0 );
            RunUpdateStatus( psThread, "" );
         }
         {
            RunUpdateStatus( psThread, "Power on %s.\nThen press 'Ok' to continue.", devices );
            bWaiting = true;
            RunKiller.Pause();
            SendMessage( psThread->hwndDlg, WM_USER_RUN_OKON, 0, 0 );
            RunKiller.Check();
            SendMessage( psThread->hwndDlg, WM_USER_RUN_OKOFF, 0, 0 );
            RunUpdateStatus( psThread, "" );
         }
      }

      do
      {
         {
            char condition[1000] = "";
            {
               switch ( TYPE[i][0] )
               {
                  case 'i':
                  {
                     sprintfsafe( condition, sizeof(condition), "dynamic manometer reaches: %.3f", CFMTOP*1.05 );
                     break;
                  }
                  case 'f':
                  {
                     strcpyarray( condition, "static manometer reaches: - 0.05" );
                     break;
                  }
                  case 'r':
                  {
                     strcpyarray( condition, "test parameters are reached." );
                     break;
                  }
               }
            }
            RunUpdateStatus( psThread, "Adjust blower speed until %s\nThen press 'Ok' to continue.", condition );
            bWaiting = true;
            RunKiller.Pause();
            SendMessage( psThread->hwndDlg, WM_USER_RUN_OKON, 0, 0 );
            RunKiller.Check();
            SendMessage( psThread->hwndDlg, WM_USER_RUN_OKOFF, 0, 0 );
            RunUpdateStatus( psThread, "" );
         }

         if ( AbType == ABTYPE_001 )
         {
            switch ( TYPE[i][0] )
            {
               case 'f':
               {
                  const double cfm = GetAverageCFM( psThread );
                  {
                     char message[1024] = "";
                     bool bTerminate = false;
                     {
                        if ( cfm > LL )
                        {
                           strcpyarray( message,
                              "WARNING!  Calibrated limits has been exceeded and errors may occur."
                           );
                        }
                        else if ( cfm/LL*8 > pp )
                        {
                           strcpyarray( message,
                              "ERROR!  Manometer maximum pressure has been exceeded."
                           );
                           bTerminate = true;
                        }
                     }
                     if ( *message )
                     {
                        BeepError();
                        BeepWarning();
                        BeepError();
                        if ( bTerminate && ! DEMO )
                        {
                           throw DangerException( message );
                        }
                        RunUpdateStatus( psThread, message );
                     }
                  }

                  break;
               }
            }
            RunUpdateStatus( psThread, "" );
         }

         RunUpdateStatus( psThread, "Running test (no more user input required)..." );
         switch ( TYPE[i][0] )
         {
            case 'r':
            {
               const double avgCFM = GetAverageCFM( psThread );
               const double avgPRESUR = GetAveragePressure( psThread );
               RunUpdateStatus( psThread, "Test is complete:  Average CFM = %.3f   Average Pressure = %.4f\nPress 'Ok' to repeat.", avgCFM, avgPRESUR );
               break;
            }
            default:
            {
               bool bCompleted = false;
               {
                  int seconds = VALVE_DELAY_SECONDS;
                  if ( DEMO )
                  {
                     seconds = 2;
                  }
                  RunUpdateStatus( psThread, "\nBegan closing valve..." );
                  BeginClosingValve();
                  {
                     for ( TimerSeconds timer( seconds ); seconds > 0; seconds = timer.Wait() )
                     {
#if KEVIN_CASH
                        const double dPressure = GetPressure();
                        RunUpdateStatus( psThread, "\nClosing valve for %d more seconds (static pressure=%.4f) ...", seconds, dPressure );
#else
                        RunUpdateStatus( psThread, "\nClosing valve for %d more seconds...", seconds );
#endif
                     }
                  }
                  RunUpdateStatus( psThread, "\nStopped closing valve..." );
                  Reset();
               }
               {
                  // ****** open airvalve until cfm=limit or pressure=0 *******
                  {
                     for ( int k = 0; ( k < MAXINCREMENTS ) && ! bCompleted; ++k )
                     {
                        const int j = IC[i];

                        {
                           int seconds = 7;
                           if ( DEMO )
                           {
                              seconds = 2;
                           }
                           {
                              for ( TimerSeconds timer( seconds ); seconds > 0; seconds = timer.Wait() )
                              {
                                 RunUpdateStatus( psThread, "\nPausing to allow airflow stabilization for %d more seconds...", seconds );
                              }
                           }
                        }

                        double dPressure = BADFLOAT;
                        double dCFM = BADFLOAT;
                        {
                           switch ( TYPE[i][0] )
                           {
                              case 'i':
                              {
                                 dCFM = GetAverageCFM( psThread );
                                 dPressure = GetAveragePressure( psThread );
                                 if ( dCFM > CFMTOP )
                                 {
                                    bCompleted = true;
                                 }
                                 break;
                              }
                              case 'f':
                              {
                                 dCFM = GetAverageCFM( psThread );
                                 dPressure = GetAveragePressure( psThread );
                                 if ( dPressure < -0.02 )
                                 {
                                    bCompleted = true;
                                 }
                                 break;
                              }
                           }
                        }
                        if ( DEMO )
                        {
                           bCompleted = j > 5;
                        }

                        if ( bCompleted && ( TYPE[i][0] == 'f' ) )
                        {
                           break;
                        }

                        CFM[i][j] = dCFM;
                        PRESUR[i][j] = dPressure;

                        if ( withPower[i] )
                        {
                           switch ( TYPE[i][0] )
                           {
                              case 'f':
                              {
                                 {
                                    VOLTS[i][j] = getVoltage();
                                    AMPS[i][j] = getCurrent();
                                    WATTS[i][j] = VOLTS[i][j] * AMPS[i][j];
                                 }
                                 break;
                              }
                           }
                        }

                        Mutex.Request();
                        if ( ! SkipStep( i ) )
                        {
                           IC[i] = j + 1;
                           Calculate();
                        }
                        Mutex.Release();
                        RunUpdateStatus( psThread, "Step #%d     CFM = %.3f    Pressure = %.4f", IC[i], CFM[i][j], PRESUR[i][j] );
                        InvalidateRect( hwndMain, 0, TRUE );

                        if ( bCompleted && ( TYPE[i][0] == 'i' ) )
                        {
                           break;
                        }

                        PulseValveOpen( psThread );
                     }
                  }
               }

               if ( bCompleted )
               {
                  RunUpdateStatus( psThread, "Test is complete." );
               }
               else
               {
                  switch ( TYPE[i][0] )
                  {
                     case 'i':
                     {
                        RunUpdateStatus( psThread,
                           "Number of steps exceeded maximum of %d.\n"
                           "To correct, decrease input value of CFM and rerun.",
                           MAXINCREMENTS
                        );
                        break;
                     }
                     case 'f':
                     {
                        RunUpdateStatus( psThread,
                           "Number of steps exceeded maximum of %d.\n"
                           "To correct, increase increment.",
                           MAXINCREMENTS
                        );
                        break;
                     }
                  }
               }

               break;
            }
         }

         BeepInfo();

         if ( TYPE[i][0] == 'r' )
         {
            bWaiting = true;
            RunKiller.Pause();
         }
         {
            const BOOL bSuccess = PostMessage( psThread->hwndDlg, WM_USER_RUN_COMPLETE, 0, 0 );
            winassert( bSuccess );
         }
      }
      while ( TYPE[i][0] == 'r' );
   }
   catch( KillerException )
   {
      {
         const BOOL bSuccess = PostMessage( psThread->hwndDlg, WM_USER_RUN_INTERRUPTED, 0, 0 );
         winassert( bSuccess );
      }
   }
   catch( SerialException ex )
   {
      BeepError();
      BeepWarning();
      BeepError();

      SendMessage( psThread->hwndDlg, WM_USER_RUN_UPDATE_STATUS, WPARAM(ex.Info()), LPARAM("Sorry, you will have to restart the test... ") );

      {
         const BOOL bSuccess = PostMessage( psThread->hwndDlg, WM_USER_RUN_DIED, 0, 0 );
         winassert( bSuccess );
      }
   }
   catch( DangerException ex )
   {
      SendMessage( psThread->hwndDlg, WM_USER_RUN_UPDATE_STATUS, WPARAM(ex.Info()), LPARAM("Sorry, you will have to restart the test... ") );

      {
         const BOOL bSuccess = PostMessage( psThread->hwndDlg, WM_USER_RUN_DIED, 0, 0 );
         winassert( bSuccess );
      }
   }
   catch ( char* message )
   {
      printf( "%s\n", message );
      MsgException( "EXCEPTION (thread)", "%s\n\nReport this to your programmer!!!", message );
      throw;
   }
   catch ( ... )
   {
      const char*const message = "UNKNOWN EXCEPTION";
      printf( "%s\n", message );
      MsgException( "EXCEPTION (thread)", "%s\n\nReport this to your programmer!!!", message );
      throw;
   }

   try
   {
      Reset();
   }
   catch ( ... )
   {
   }

   delete psThread, psThread = 0;
}

static INT_PTR CALLBACK RunDlgProc( HWND hwnd, UINT message, WPARAM wParam, LPARAM lParam )
{
   static HANDLE handleThread = 0;

   switch ( message )
   {
      case WM_USER_RUN_UPDATE_STATUS:
      {
         const char* psz1 = reinterpret_cast<char*>( wParam );
         const char* psz2 = reinterpret_cast<char*>( lParam );
         if ( psz1 )
         {
            SetDlgItemText( hwnd, ID_TEXT_STATUS, psz1 );
         }
         if ( psz2 )
         {
            SetDlgItemText( hwnd, ID_TEXT_STATUS_2, psz2 );
         }
         else
         {
            SetDlgItemText( hwnd, ID_TEXT_STATUS_2, "" );
         }
         return 0;
      }

      case WM_USER_RUN_COMPLETE:
      {
         const int i = 0;

         EnableDisableWindow( GetDlgItem( hwnd, IDOK ), true );
         if ( GetFocus() == GetDlgItem( hwnd, IDCANCEL ) )
         {
            SetFocus( GetDlgItem( hwnd, IDOK ) );
         }
         if ( TYPE[i][0] != 'r' )
         {
            EnableDisableWindow( GetDlgItem( hwnd, IDCANCEL ), false );
         }
         if ( hdcAutoPrint )
         {
            const char* p = 0;
            {
               p = strrchr( filename[i], '\\' );
               if ( p )
               {
                  ++p;
               }
            }
            if ( ! p )
            {
               p = filename[i];
            }

            const char*const docname = *FIG ? FIG : ( *p ? p : "AIRBENCH" );
            struct DrawGraphStruct s( true, true );
            TurnHourglassOn();
            DoPrint( hdcAutoPrint, DrawGraph, &s, docname );
            TurnHourglassOff();

            DeleteDC( hdcAutoPrint );
            hdcAutoPrint = 0;

            SendMessage( hwnd, WM_USER_RUN_UPDATE_STATUS, WPARAM(""), LPARAM("Test is complete, and graph was printed.") );
         }
         return 0;
      }

      case WM_USER_RUN_DIED:
      {
         EnableDisableWindow( GetDlgItem( hwnd, IDOK ), true );
         if ( GetFocus() == GetDlgItem( hwnd, IDCANCEL ) )
         {
            SetFocus( GetDlgItem( hwnd, IDOK ) );
         }
         EnableDisableWindow( GetDlgItem( hwnd, IDCANCEL ), false );
         return 0;
      }

      case WM_USER_RUN_INTERRUPTED:
      {
         DestroyWindow( hwnd );
         return 0;
      }

      case WM_USER_RUN_OKON:
      {
         EnableDisableWindow( GetDlgItem( hwnd, IDOK ), true );
         if ( GetFocus() == GetDlgItem( hwnd, IDCANCEL ) )
         {
            SetFocus( GetDlgItem( hwnd, IDOK ) );
         }
         return 0;
      }

      case WM_USER_RUN_OKOFF:
      {
         if ( GetFocus() == GetDlgItem( hwnd, IDOK ) )
         {
            SetFocus( GetDlgItem( hwnd, IDCANCEL ) );
         }
         EnableDisableWindow( GetDlgItem( hwnd, IDOK ), false );
         return 0;
      }

      case WM_INITDIALOG:
      {
         CenterWindow( hwnd );
         EnableDisableMenuItem( GetSystemMenu(hwnd,FALSE), SC_CLOSE, false );

         const int i = 0;

         {
            switch ( TYPE[i][0] )
            {
               case 'i':
               {
                  SetWindowText( hwnd, "Impedance test" );
                  break;
               }
               case 'r':
               {
                  SetWindowText( hwnd, "Flow rate test" );
                  break;
               }
               case 'f':
               {
                  SetWindowText( hwnd, "Fan performance test" );
                  break;
               }
            }
         }

         RunKiller.Start();

         RunThreadStruct* psThread = new RunThreadStruct;
         psThread->hwndDlg = hwnd;

         {
            const bool b = StartWaitableThread( RunThread, psThread, &handleThread );
            assert( b );
            assert( !!handleThread );
         }

         return TRUE;
      }

      case WM_COMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         const WORD wCode = HIWORD(wParam);
         switch ( wCmd )
         {
            case IDOK:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     if ( bWaiting )
                     {
                        bWaiting = false;
                        RunKiller.Resume();
                     }
                     else
                     {
                        DestroyWindow( hwnd );
                     }
                     return TRUE;
                  }
               }
               return FALSE;
            }
            case IDCANCEL:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     if ( ! MsgIsYes( MsgYesNoQuery( "Terminate?", "Are you sure you want to terminate the test?" ) ) )
                     {
                        return TRUE;
                     }
                     RunKiller.Stop();
                     return TRUE;
                  }
               }
               return FALSE;
            }
         }
         return FALSE;
      }

      case WM_SYSCOMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         switch (wCmd)
         {
            case SC_CLOSE:
            {
               return TRUE;
            }
         }
         return FALSE;
      }

      case WM_DESTROY:
      {
         hwndDlgRun = 0;
         if ( handleThread )
         {
            WaitForThreadFinished( handleThread );
            handleThread = 0;
         }
         SendMessage( hwndMain, WM_USER_RUN_STOPPED, 0, 0 );
         ActivateWindow( hwndMain );
         break;
      }
   }

   return FALSE;
}

static void Run( HWND hwndParent )
{
   hwndDlgRun = CreateDialogParam( hinst, MAKEINTRESOURCE(ID_DLG_RUN), hwndParent, RunDlgProc, 0 );
   winassert( hwndDlgRun );
   ShowWindow( hwndDlgRun, SW_NORMAL );
}

//--------------------------------------------------------------------

static INT_PTR CALLBACK DeleteDlgProc( HWND hwnd, UINT message, WPARAM wParam, LPARAM lParam )
{
   static bool bUsedTemp[MAXFILES] = { 0 };
   static int map[MAXFILES] = { 0 };

   switch ( message )
   {
      case WM_INITDIALOG:
      {
         CenterWindow( hwnd );
         EnableDisableMenuItem( GetSystemMenu(hwnd,FALSE), SC_CLOSE, false );

         Mutex.Request();
         memcpy( bUsedTemp, bUsed, sizeof(bUsedTemp) );
         Mutex.Release();

         int index = 1;
         {
            for ( int i = 1; i < MAXFILES; ++i )
            {
               if ( bUsed[i] )
               {
                  map[index] = i;
                  {
                     HWND hwndText = GetDlgItem( hwnd, ID_TEXT_BASE+index );
                     SetWindowText( hwndText, filename[i] );
                  }
                  {
                     HWND hwndCheck = GetDlgItem( hwnd, ID_CHECK_BASE+index );
                     SetWindowTextf( hwndCheck, "&%c", aMarker[i] );
                  }
                  ++index;
               }
            }
         }
         {
            for ( ; index < MAXFILES; ++index )
            {
               ShowHideWindow( GetDlgItem( hwnd, ID_TEXT_BASE+index ), false );
               ShowHideWindow( GetDlgItem( hwnd, ID_CHECK_BASE+index ), false );
            }
         }

         return TRUE;
      }

      case WM_COMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         const WORD wCode = HIWORD(wParam);
         switch ( wCmd )
         {
            case IDOK:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     EndDialog( hwnd, wCmd );
                     return TRUE;
                  }
               }
               return FALSE;
            }

            case IDCANCEL:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     Mutex.Request();
                     memcpy( bUsed, bUsedTemp, sizeof(bUsed) );
                     Mutex.Release();
                     InvalidateRect( hwndMain, 0, TRUE );
                     EndDialog( hwnd, wCmd );
                     return TRUE;
                  }
               }
               return FALSE;
            }

            case ID_CHECK_1:
            case ID_CHECK_2:
            case ID_CHECK_3:
            case ID_CHECK_4:
            case ID_CHECK_5:
            case ID_CHECK_6:
            case ID_CHECK_7:
            case ID_CHECK_8:
            case ID_CHECK_9:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     const int i = map[wCmd - ID_CHECK_BASE];

                     Mutex.Request();
                     bUsed[i] = ! bUsed[i];
                     Mutex.Release();

                     CheckUncheckButton( hwnd, wCmd, ! bUsed[i] );

                     InvalidateRect( hwndMain, 0, TRUE );
                     break;
                  }
               }
               break;
            }
         }
         return FALSE;
      }

      case WM_SYSCOMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         switch (wCmd)
         {
            case SC_CLOSE:
            {
               return TRUE;
            }
         }
         return FALSE;
      }

      case WM_CTLCOLORSTATIC:
      {
         const HWND hwndControl = reinterpret_cast<HWND>(lParam);
         const int idControl = GetDlgCtrlID( hwndControl );
         const HDC hdcControl = reinterpret_cast<HDC>(wParam);
         const COLORREF colorBackground = GetSysColor( COLOR_3DFACE );
         const HBRUSH hbrushBackground = GetSysColorBrush( COLOR_3DFACE );
         {
            switch ( idControl )
            {
               case ID_TEXT_1:
               case ID_TEXT_2:
               case ID_TEXT_3:
               case ID_TEXT_4:
               case ID_TEXT_5:
               case ID_TEXT_6:
               case ID_TEXT_7:
               case ID_TEXT_8:
               case ID_TEXT_9:
               {
                  const int i = map[idControl - ID_TEXT_BASE];
                  SetTextColor( hdcControl, aColor[i] );
                  SetBkColor( hdcControl, colorBackground );
                  return reinterpret_cast<INT_PTR>(hbrushBackground);
               }
            }
         }
         return FALSE;
      }

   }

   return FALSE;
}

static void Delete( HWND hwndParent )
{
   const INT_PTR rc = DialogBoxParam( hinst, MAKEINTRESOURCE(ID_DLG_DELETE), hwndParent, DeleteDlgProc, 0 );
   winassert( rc > 0 );
}

//--------------------------------------------------------------------

static INT_PTR CALLBACK NamesDlgProc( HWND hwnd, UINT message, WPARAM wParam, LPARAM lParam )
{
   switch ( message )
   {
      case WM_INITDIALOG:
      {
         CenterWindow( hwnd );
         EnableDisableMenuItem( GetSystemMenu(hwnd,FALSE), SC_CLOSE, false );

         {
            const HWND hwndEF = GetDlgItem( hwnd, ID_ENTRY_PLOTNAME );
            SetWindowText( hwndEF, FIG );
            Edit_LimitText( hwndEF, sizeof(FIG)-1 );
         }

         {
            const HWND hwndEF = GetDlgItem( hwnd, ID_ENTRY_YOURNAME );
            SetWindowText( hwndEF, YOURNAM );
            Edit_LimitText( hwndEF, sizeof(YOURNAM)-1 );
         }

         return TRUE;
      }

      case WM_COMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         const WORD wCode = HIWORD(wParam);
         switch ( wCmd )
         {
            case IDOK:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     GetDlgItemText( hwnd, ID_ENTRY_PLOTNAME, FIG, sizeof(FIG) );
                     GetDlgItemText( hwnd, ID_ENTRY_YOURNAME, YOURNAM, sizeof(YOURNAM) );

                     EndDialog( hwnd, wCmd );
                     return TRUE;
                  }
               }
               return FALSE;
            }

            case IDCANCEL:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     EndDialog( hwnd, wCmd );
                     return TRUE;
                  }
               }
               return FALSE;
            }

         }
         return FALSE;
      }

      case WM_SYSCOMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         switch (wCmd)
         {
            case SC_CLOSE:
            {
               return TRUE;
            }
         }
         return FALSE;
      }
   }

   return FALSE;
}

static bool Names( HWND hwndParent )
{
   const INT_PTR rc = DialogBoxParam( hinst, MAKEINTRESOURCE(ID_DLG_NAMES), hwndParent, NamesDlgProc, 0 );
   winassert( rc > 0 );
   return ( rc == IDOK );
}

//------------------------------------------------------------------

static INT_PTR CALLBACK ScaleDlgProc( HWND hwnd, UINT message, WPARAM wParam, LPARAM lParam )
{
   switch ( message )
   {
      case WM_INITDIALOG:
      {
         CenterWindow( hwnd );
         EnableDisableMenuItem( GetSystemMenu(hwnd,FALSE), SC_CLOSE, false );

         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFMSCALE );
            winassert( hwndEdit );

            SubclassFieldReal( hwndEdit, formatCFMSCALE, precisionCFMSCALE, minallowedCFMSCALE, maxallowedCFMSCALE );

            Edit_LimitText( hwndEdit, maxlengthCFMSCALE );

            SetWindowTextf( hwndEdit, formatCFMSCALE, CFMSCALE );
         }
         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_PRESURSCALE );
            winassert( hwndEdit );

            SubclassFieldReal( hwndEdit, formatPRESURSCALE, precisionPRESURSCALE, minallowedPRESURSCALE, maxallowedPRESURSCALE );

            Edit_LimitText( hwndEdit, maxlengthPRESURSCALE );

            SetWindowTextf( hwndEdit, formatPRESURSCALE, PRESURSCALE );
         }

         return TRUE;
      }

      case WM_NOTIFY:
      {
         const int id = wParam;
         const NMHDR*const pnmhdr = reinterpret_cast<NMHDR*>(lParam);

         switch ( id )
         {
            case ID_SPIN_CFMSCALE:
            {
               switch ( pnmhdr->code )
               {
                  case UDN_DELTAPOS:
                  {
                     const NMUPDOWN* pUpDown = reinterpret_cast<NMUPDOWN*>(lParam);
                     const int iDelta = pUpDown->iDelta;
                     if ( iDelta < 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFMSCALE, WM_KEYDOWN, VK_UP, 0 );
                     }
                     else if ( iDelta > 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFMSCALE, WM_KEYDOWN, VK_DOWN, 0 );
                     }
                     break;
                  }
               }
               break;
            }
            case ID_SPIN_PRESURSCALE:
            {
               switch ( pnmhdr->code )
               {
                  case UDN_DELTAPOS:
                  {
                     const NMUPDOWN* pUpDown = reinterpret_cast<NMUPDOWN*>(lParam);
                     const int iDelta = pUpDown->iDelta;
                     if ( iDelta < 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_PRESURSCALE, WM_KEYDOWN, VK_UP, 0 );
                     }
                     else if ( iDelta > 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_PRESURSCALE, WM_KEYDOWN, VK_DOWN, 0 );
                     }
                     break;
                  }
               }
               break;
            }
         }
         break;
      }

      case WM_COMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         const WORD wCode = HIWORD(wParam);

         switch ( wCmd )
         {
            case IDOK:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     double tempCFMSCALE = CFMSCALE;
                     {
                        const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFMSCALE );
                        winassert( hwndEdit );

                        char buffer[80+1] = "";
                        GetWindowText( hwndEdit, buffer, sizeof(buffer) );
                        tempCFMSCALE = StringToFloat( buffer, precisionCFMSCALE, minallowedCFMSCALE, maxallowedCFMSCALE );

                        if ( ! IsValid(tempCFMSCALE) )
                        {
                           SetFocus( hwndEdit );
                           BeepError();
                           return TRUE;
                        }
                     }

                     double tempPRESURSCALE = PRESURSCALE;
                     {
                        const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_PRESURSCALE );
                        winassert( hwndEdit );

                        char buffer[80+1] = "";
                        GetWindowText( hwndEdit, buffer, sizeof(buffer) );
                        tempPRESURSCALE = StringToFloat( buffer, precisionPRESURSCALE, minallowedPRESURSCALE, maxallowedPRESURSCALE );

                        if ( ! IsValid(tempPRESURSCALE) )
                        {
                           SetFocus( hwndEdit );
                           BeepError();
                           return TRUE;
                        }
                     }

                     CFMSCALE = tempCFMSCALE;
                     PRESURSCALE = tempPRESURSCALE;

                     EndDialog( hwnd, wCmd );
                     return TRUE;
                  }
               }
               return FALSE;
            }

            case IDCANCEL:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     EndDialog( hwnd, wCmd );
                     return TRUE;
                  }
               }
               return FALSE;
            }

         }

         return FALSE;
      }

      case WM_SYSCOMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         switch (wCmd)
         {
            case SC_CLOSE:
            {
               return TRUE;
            }
         }
         return FALSE;
      }
   }

   return FALSE;
}

static bool Scale( HWND hwndParent )
{
   const INT_PTR rc = DialogBoxParam( hinst, MAKEINTRESOURCE(ID_DLG_SCALE), hwndParent, ScaleDlgProc, 0 );
   winassert( rc > 0 );
   return ( rc == IDOK );
}

//--------------------------------------------------------------------

static void FixOverlayAndBestCurveMenus()
{
   {
      const bool bUsingGraph = ( TYPE[0][0] != 'r' );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_PRINTGRAPH         , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_EXPORT             , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_OVERLAY            , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_ADD                , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_DELETE             , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_GRAPH              , bUsingGraph );
      // EnableDisableMenuItem( GetMenu(hwndMain), IDM_BESTFITCURVE       , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_NAMES              , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_SCALE              , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_FONT               , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_FONT_ARIAL         , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_FONT_COURIERNEW    , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_FONT_TIMESNEWROMAN , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_FONT_BOLD          , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_FONT_ITALIC        , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_FONT_UP            , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_FONT_DOWN          , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_COPY               , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_CLIPBOARD          , bUsingGraph );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_SAVEFILE           , bUsingGraph );
      if ( ! bUsingGraph )
      {
         DrawMenuBar( hwndMain );
         return;
      }
   }
   {
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_ADD, false );
      {
         for ( int itemp = 1; itemp < MAXFILES; ++itemp )
         {
            if ( ! bUsed[itemp] )
            {
               EnableDisableMenuItem( GetMenu(hwndMain), IDM_ADD, true );
               break;
            }
         }
      }
   }
   {
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_DELETE, false );
      {
         for ( int itemp = 1; itemp < MAXFILES; ++itemp )
         {
            if ( bUsed[itemp] )
            {
               EnableDisableMenuItem( GetMenu(hwndMain), IDM_DELETE, true );
               break;
            }
         }
      }
   }
   // {
   //    bool bAllowBestCurve = false;
   //    {
   //       for ( int i = MAXFILES-1; i >= 0; --i )
   //       {
   //          if ( ! bUsed[i] )
   //          {
   //             continue;
   //          }
   //          {
   //             switch ( TYPE[i][0] )
   //             {
   //                case 'i':
   //                {
   //                   bAllowBestCurve = true;
   //                   break;
   //                }
   //             }
   //          }
   //       }
   //    }
   //    if ( bAllowBestCurve )
   //    {
   //       EnableDisableMenuItem( GetMenu(hwndMain), IDM_BESTFITCURVE, true );
   //       if ( bBestFitCurve )
   //       {
   //          CheckUncheckMenuItem( GetMenu(hwndMain), IDM_BESTFITCURVE, true );
   //       }
   //       else
   //       {
   //          CheckUncheckMenuItem( GetMenu(hwndMain), IDM_BESTFITCURVE, false );
   //       }
   //    }
   //    else
   //    {
   //       EnableDisableMenuItem( GetMenu(hwndMain), IDM_BESTFITCURVE, false );
   //       CheckUncheckMenuItem( GetMenu(hwndMain), IDM_BESTFITCURVE, false );
   //    }
   // }
   DrawMenuBar( hwndMain );
}

static void FixFontSizeMenuItems( HWND hwnd )
{
   const HMENU hmenu = GetMenu( hwnd );
   {
      char buffer[80] = "";
      sprintfsafe( buffer, sizeof(buffer), "&Larger than %d\tCtrl-+", fontsize );
      ModifyMenu( hmenu, IDM_FONT_UP, MF_BYCOMMAND | MF_STRING, IDM_FONT_UP, buffer );
   }
   {
      char buffer[80] = "";
      sprintfsafe( buffer, sizeof(buffer), "&Smaller than %d\tCtrl--", fontsize );
      ModifyMenu( hmenu, IDM_FONT_DOWN, MF_BYCOMMAND | MF_STRING, IDM_FONT_DOWN, buffer );
   }
}

//--------------------------------------------------------------------

static char gpibfilename[_MAX_PATH] = { 0 };

static int WriteGpibFile()
{
   FILE*const pf = fopen( gpibfilename, "w" );
   if ( ! pf )
   {
      return 0;
   }

   if ( fprintf( pf, "%d\n", gpibaddr ) < 0 )
   {
      fclose( pf );
      return 0;
   }

   if ( fprintf( pf, "%d\n", gpibaddrpower ) < 0 )
   {
      fclose( pf );
      return 0;
   }

   if ( fclose( pf ) != 0 )
   {
      return 0;
   }

   return 1;
}

static bool SaveGpibFile( void )
{
   if ( ! WriteGpibFile() )
   {
      MsgOkError( "Error!", "Could not write to gpib file\n\n%s", gpibfilename );
      return false;
   }
   else
   {
      return true;
   }
}

static void ReadGpibFile( void )
{
   char string[_MAX_PATH] = "";

   FILE*const stream = fopen( gpibfilename, "r" );
   if ( ! stream )
   {
      return;
   }

   if ( getline( string, sizeof(string), stream ) )
   {
      gpibaddr = atoi(string);
      LowerBound( gpibaddr, GPIB_FIRST );
      UpperBound( gpibaddr, GPIB_LAST );
   }

   if ( getline( string, sizeof(string), stream ) )
   {
      gpibaddrpower = atoi(string);
      LowerBound( gpibaddr, 0 );
      UpperBound( gpibaddr, GPIB_LAST );
   }

   fclose( stream );
}

//--------------------------------------------------------------------

static char serialfilename[_MAX_PATH] = { 0 };

static int WriteSerialFile()
{
   FILE*const pf = fopen( serialfilename, "w" );
   if ( ! pf )
   {
      return 0;
   }

   if ( fprintf( pf, "%s\n", aPorts[portPressure] ) < 0 )
   {
      fclose( pf );
      return 0;
   }

   if ( fprintf( pf, "%s\n", aPorts[portCFM] ) < 0 )
   {
      fclose( pf );
      return 0;
   }

   if ( fclose( pf ) != 0 )
   {
      return 0;
   }

   return 1;
}

static bool SaveSerialFile( void )
{
   if ( ! WriteSerialFile() )
   {
      MsgOkError( "Error!", "Could not write to serial file\n\n%s", serialfilename );
      return false;
   }
   else
   {
      return true;
   }
}

static void ReadSerialFile( void )
{
   char string[_MAX_PATH] = "";

   FILE*const stream = fopen( serialfilename, "r" );
   if ( ! stream )
   {
      return;
   }

   if ( getline( string, sizeof(string), stream ) )
   {
      {
         for ( int i = 0; i < DIMENSION(aPorts); ++i )
         {
            if ( stricmp( string, aPorts[i] ) == 0 )
            {
               portPressure = i;
            }
         }
      }
   }

   if ( getline( string, sizeof(string), stream ) )
   {
      {
         for ( int i = 0; i < DIMENSION(aPorts); ++i )
         {
            if ( stricmp( string, aPorts[i] ) == 0 )
            {
               portCFM = i;
            }
         }
      }
   }

   fclose( stream );
}

//-----------------------------------------------------------------

static INT_PTR CALLBACK SetupSerialDlgProc( HWND hwnd, UINT message, WPARAM wParam, LPARAM lParam )
{
   switch ( message )
   {
      case WM_INITDIALOG:
      {
         CenterWindow( hwnd );
         EnableDisableMenuItem( GetSystemMenu(hwnd,FALSE), SC_CLOSE, false );

         {
            const HWND hwndDropDown = GetDlgItem( hwnd, ID_CB_SERIAL_PRESSURE );
            winassert( hwndDropDown );

            {
               for ( int i = 0; i < DIMENSION(aPorts); ++i )
               {
                  const int Index = AddString( hwndDropDown, aPorts[i] );
                  winassert( Index >= 0 );
               }
            }

            if ( portPressure > 0 )
            {
               const int Index = ComboBox_SetCurSel( hwndDropDown, portPressure );
               winassert( Index >= 0 );
            }
         }

         {
            const HWND hwndDropDown = GetDlgItem( hwnd, ID_CB_SERIAL_CFM );
            winassert( hwndDropDown );

            {
               for ( int i = 0; i < DIMENSION(aPorts); ++i )
               {
                  const int Index = AddString( hwndDropDown, aPorts[i] );
                  winassert( Index >= 0 );
               }
            }

            if ( portCFM > 0 )
            {
               const int Index = ComboBox_SetCurSel( hwndDropDown, portCFM );
               winassert( Index >= 0 );
            }
         }

         return TRUE;
      }

      case WM_COMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         const WORD wCode = HIWORD(wParam);
         switch ( wCmd )
         {
            case IDOK:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     int indexPressure = -1;
                     {
                        const HWND hwndDropDown = GetDlgItem( hwnd, ID_CB_SERIAL_PRESSURE );
                        winassert( hwndDropDown );

                        indexPressure = ComboBox_GetCurSel( hwndDropDown );
                        if ( indexPressure <= 0 )
                        {
                           SetDlgItemTextf( hwnd, ID_TEXT_SERIAL_ERROR, "You must select a port for reading pressure!" );
                           BeepError();
                           SetFocus( hwndDropDown );
                           return TRUE;
                        }
                     }

                     int indexCFM = -1;
                     {
                        const HWND hwndDropDown = GetDlgItem( hwnd, ID_CB_SERIAL_CFM );
                        winassert( hwndDropDown );

                        indexCFM = ComboBox_GetCurSel( hwndDropDown );
                        if ( indexCFM <= 0 )
                        {
                           SetDlgItemTextf( hwnd, ID_TEXT_SERIAL_ERROR, "You must select a port for reading CFM!" );
                           BeepError();
                           SetFocus( hwndDropDown );
                           return TRUE;
                        }
                     }

                     {
                        if ( indexCFM == indexPressure )
                        {
                           SetDlgItemTextf( hwnd, ID_TEXT_SERIAL_ERROR, "You must select different ports for reading pressure and CFM!" );
                           BeepError();
                           SetFocus( GetDlgItem( hwnd, ID_CB_SERIAL_PRESSURE ) );
                           return TRUE;
                        }
                     }

                     portPressure = indexPressure;
                     portCFM = indexCFM;

                     SaveSerialFile();
                     EndDialog( hwnd, wCmd );
                     return TRUE;
                  }
               }
               return FALSE;
            }

            case IDCANCEL:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     EndDialog( hwnd, wCmd );
                     return TRUE;
                  }
               }
               return FALSE;
            }

            case ID_CB_SERIAL_PRESSURE:
            case ID_CB_SERIAL_CFM:
            {
               switch ( wCode )
               {
                  case CBN_EDITCHANGE:
                  {
                     SetDlgItemText( hwnd, ID_TEXT_SERIAL_ERROR, "" );
                     return TRUE;
                  }
               }
               break;
            }

         }
         return FALSE;
      }

      case WM_SYSCOMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         switch (wCmd)
         {
            case SC_CLOSE:
            {
               return TRUE;
            }
         }
         return FALSE;
      }

      case WM_CTLCOLORSTATIC:
      {
         const HWND hwndControl = reinterpret_cast<HWND>(lParam);
         const HDC hdcControl = reinterpret_cast<HDC>(wParam);
         const COLORREF colorBackground = GetSysColor( COLOR_3DFACE );
         const HBRUSH hbrushBackground = GetSysColorBrush( COLOR_3DFACE );
         const HWND hwndMessage = GetDlgItem( hwnd, ID_TEXT_SERIAL_ERROR );
         if ( hwndControl == hwndMessage )
         {
            SetTextColor( hdcControl, CLR_RED );
            SetBkColor( hdcControl, colorBackground );
            return reinterpret_cast<INT_PTR>(hbrushBackground);
         }
         return FALSE;
      }

   }

   return FALSE;
}

static bool SetupSerial( HWND hwndParent )
{
   const INT_PTR rc = DialogBoxParam( hinst, MAKEINTRESOURCE(ID_DLG_SERIAL), hwndParent, SetupSerialDlgProc, 0 );
   winassert( rc > 0 );
   return ( rc == IDOK );
}

//--------------------------------------------------------------------

static char cfgfilename[_MAX_PATH] = { 0 };

static int WriteConfigFile()
{
   FILE*const pf = fopen( cfgfilename, "w" );
   if ( ! pf )
   {
      return 0;
   }

   char line[_MAX_PATH] = "";

   {
      stringblank( line );
      if ( IsValidFor_LL(LL) )
      {
         sprintfsafe( line, sizeof(line), format_LL, LL );
      }
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return 0;
      }
   }

   {
      stringblank( line );
      if ( IsValidFor_bb(bb) )
      {
         sprintfsafe( line, sizeof(line), format_bb, bb );
      }
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return 0;
      }
   }

   {
      stringblank( line );
      if ( IsValidFor_cc(cc) )
      {
         sprintfsafe( line, sizeof(line), format_cc, cc );
      }
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return 0;
      }
   }

   {
      stringblank( line );
      if ( IsValidFor_vv(vv) )
      {
         sprintfsafe( line, sizeof(line), format_vv, vv );
      }
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return 0;
      }
   }

   {
      stringblank( line );
      if ( IsValidFor_pp(pp) )
      {
         sprintfsafe( line, sizeof(line), format_pp, pp );
      }
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return 0;
      }
   }

   {
      stringblank( line );
      if ( IsValidFor_vv(vvstat) )
      {
         sprintfsafe( line, sizeof(line), format_vv, vvstat );
      }
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return 0;
      }
   }

   {
      stringblank( line );
      if ( IsValidFor_pp(ppstat) )
      {
         sprintfsafe( line, sizeof(line), format_pp, ppstat );
      }
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return 0;
      }
   }

   {
      stringblank( line );
      if ( IsValidFor_off(offstat) )
      {
         sprintfsafe( line, sizeof(line), format_off, offstat );
      }
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return 0;
      }
   }

   {
      stringblank( line );
      if ( IsValidFor_off(off) )
      {
         sprintfsafe( line, sizeof(line), format_off, off );
      }
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return 0;
      }
   }

   if ( fclose( pf ) != 0 )
   {
      return 0;
   }

   return 1;
}

static bool SaveConfigFile( void )
{
   if ( ! WriteConfigFile() )
   {
      MsgOkError( "Error!", "Could not write to parameters config file\n\n%s", cfgfilename );
      return false;
   }
   else
   {
      return true;
   }
}

static void ReadConfigFile( void )
{
   LL = bb = cc = vv = pp = off = vvstat = ppstat = offstat = BADFLOAT;

   char string[_MAX_PATH] = "";

   FILE*const stream = fopen( cfgfilename, "r" );
   if ( ! stream )
   {
      return;
   }

   if ( getline( string, sizeof(string), stream ) )
   {
      LL = StringToFloat( string, precision_LL, min_LL, max_LL );
   }

   if ( getline( string, sizeof(string), stream ) )
   {
      bb = StringToFloat( string, precision_bb, min_bb, max_bb );
   }

   if ( getline( string, sizeof(string), stream ) )
   {
      cc = StringToFloat( string, precision_cc, min_cc, max_cc );
   }

   if ( getline( string, sizeof(string), stream ) )
   {
      vv = StringToFloat( string, precision_vv, min_vv, max_vv );
   }

   if ( getline( string, sizeof(string), stream ) )
   {
      pp = StringToFloat( string, precision_pp, min_pp, max_pp );
   }

   if ( getline( string, sizeof(string), stream ) )
   {
      vvstat = StringToFloat( string, precision_vv, min_vv, max_vv );
   }

   if ( getline( string, sizeof(string), stream ) )
   {
      ppstat = StringToFloat( string, precision_pp, min_pp, max_pp );
   }

   if ( getline( string, sizeof(string), stream ) )
   {
      offstat = StringToFloat( string, precision_off, min_off, max_off );
   }

   if ( getline( string, sizeof(string), stream ) )
   {
      off = StringToFloat( string, precision_off, min_off, max_off );
   }

   fclose( stream );
}

//-----------------------------------------------------------------

static INT_PTR CALLBACK ConfigureDlgProc( HWND hwnd, UINT message, WPARAM wParam, LPARAM lParam )
{
   switch ( message )
   {
      case WM_INITDIALOG:
      {
         CenterWindow( hwnd );
         EnableDisableMenuItem( GetSystemMenu(hwnd,FALSE), SC_CLOSE, false );

         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_LL );
            winassert( hwndEdit );

            SubclassFieldReal( hwndEdit, format_LL, precision_LL, min_LL, max_LL );

            Edit_LimitText( hwndEdit, maxlength_LL );

            if ( IsValidFor_LL(LL) )
            {
               SetWindowTextf( hwndEdit, format_LL, LL );
            }
         }

         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_BB );
            winassert( hwndEdit );

            SubclassFieldReal( hwndEdit, format_bb, precision_bb, min_bb, max_bb );

            Edit_LimitText( hwndEdit, maxlength_bb );

            if ( IsValidFor_bb(bb) )
            {
               SetWindowTextf( hwndEdit, format_bb, bb );
            }
         }

         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_CC );
            winassert( hwndEdit );

            SubclassFieldReal( hwndEdit, format_cc, precision_cc, min_cc, max_cc );

            Edit_LimitText( hwndEdit, maxlength_cc );

            if ( IsValidFor_cc(cc) )
            {
               SetWindowTextf( hwndEdit, format_cc, cc );
            }
         }

         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_VV );
            winassert( hwndEdit );

            SubclassFieldReal( hwndEdit, format_vv, precision_vv, min_vv, max_vv );

            Edit_LimitText( hwndEdit, maxlength_vv );

            if ( IsValidFor_vv(vv) )
            {
               SetWindowTextf( hwndEdit, format_vv, vv );
            }
         }

         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_PP );
            winassert( hwndEdit );

            SubclassFieldReal( hwndEdit, format_pp, precision_pp, min_pp, max_pp );

            Edit_LimitText( hwndEdit, maxlength_pp );

            if ( IsValidFor_pp(pp) )
            {
               SetWindowTextf( hwndEdit, format_pp, pp );
            }
         }

         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_OFF );
            winassert( hwndEdit );

            SubclassFieldReal( hwndEdit, format_off, precision_off, min_off, max_off );

            Edit_LimitText( hwndEdit, maxlength_off );

            if ( IsValidFor_off(off) )
            {
               SetWindowTextf( hwndEdit, format_off, off );
            }
         }

         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_VVSTAT );
            winassert( hwndEdit );

            SubclassFieldReal( hwndEdit, format_vv, precision_vv, min_vv, max_vv );

            Edit_LimitText( hwndEdit, maxlength_vv );

            if ( IsValidFor_vv(vvstat) )
            {
               SetWindowTextf( hwndEdit, format_vv, vvstat );
            }
         }

         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_PPSTAT );
            winassert( hwndEdit );

            SubclassFieldReal( hwndEdit, format_pp, precision_pp, min_pp, max_pp );

            Edit_LimitText( hwndEdit, maxlength_pp );

            if ( IsValidFor_pp(ppstat) )
            {
               SetWindowTextf( hwndEdit, format_pp, ppstat );
            }
         }

         {
            const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_OFFSTAT );
            winassert( hwndEdit );

            SubclassFieldReal( hwndEdit, format_off, precision_off, min_off, max_off );

            Edit_LimitText( hwndEdit, maxlength_off );

            if ( IsValidFor_off(offstat) )
            {
               SetWindowTextf( hwndEdit, format_off, offstat );
            }
         }

         return TRUE;
      }

      case WM_NOTIFY:
      {
         const int id = wParam;
         const NMHDR*const pnmhdr = reinterpret_cast<NMHDR*>(lParam);

         switch ( id )
         {
            case ID_SPIN_CFG_LL:
            {
               switch ( pnmhdr->code )
               {
                  case UDN_DELTAPOS:
                  {
                     const NMUPDOWN* pUpDown = reinterpret_cast<NMUPDOWN*>(lParam);
                     const int iDelta = pUpDown->iDelta;
                     if ( iDelta < 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_LL, WM_KEYDOWN, VK_UP, 0 );
                     }
                     else if ( iDelta > 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_LL, WM_KEYDOWN, VK_DOWN, 0 );
                     }
                     break;
                  }
               }
               break;
            }
            case ID_SPIN_CFG_BB:
            {
               switch ( pnmhdr->code )
               {
                  case UDN_DELTAPOS:
                  {
                     const NMUPDOWN* pUpDown = reinterpret_cast<NMUPDOWN*>(lParam);
                     const int iDelta = pUpDown->iDelta;
                     if ( iDelta < 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_BB, WM_KEYDOWN, VK_UP, 0 );
                     }
                     else if ( iDelta > 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_BB, WM_KEYDOWN, VK_DOWN, 0 );
                     }
                     break;
                  }
               }
               break;
            }
            case ID_SPIN_CFG_CC:
            {
               switch ( pnmhdr->code )
               {
                  case UDN_DELTAPOS:
                  {
                     const NMUPDOWN* pUpDown = reinterpret_cast<NMUPDOWN*>(lParam);
                     const int iDelta = pUpDown->iDelta;
                     if ( iDelta < 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_CC, WM_KEYDOWN, VK_UP, 0 );
                     }
                     else if ( iDelta > 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_CC, WM_KEYDOWN, VK_DOWN, 0 );
                     }
                     break;
                  }
               }
               break;
            }
            case ID_SPIN_CFG_VV:
            {
               switch ( pnmhdr->code )
               {
                  case UDN_DELTAPOS:
                  {
                     const NMUPDOWN* pUpDown = reinterpret_cast<NMUPDOWN*>(lParam);
                     const int iDelta = pUpDown->iDelta;
                     if ( iDelta < 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_VV, WM_KEYDOWN, VK_UP, 0 );
                     }
                     else if ( iDelta > 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_VV, WM_KEYDOWN, VK_DOWN, 0 );
                     }
                     break;
                  }
               }
               break;
            }
            case ID_SPIN_CFG_PP:
            {
               switch ( pnmhdr->code )
               {
                  case UDN_DELTAPOS:
                  {
                     const NMUPDOWN* pUpDown = reinterpret_cast<NMUPDOWN*>(lParam);
                     const int iDelta = pUpDown->iDelta;
                     if ( iDelta < 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_PP, WM_KEYDOWN, VK_UP, 0 );
                     }
                     else if ( iDelta > 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_PP, WM_KEYDOWN, VK_DOWN, 0 );
                     }
                     break;
                  }
               }
               break;
            }
            case ID_SPIN_CFG_OFF:
            {
               switch ( pnmhdr->code )
               {
                  case UDN_DELTAPOS:
                  {
                     const NMUPDOWN* pUpDown = reinterpret_cast<NMUPDOWN*>(lParam);
                     const int iDelta = pUpDown->iDelta;
                     if ( iDelta < 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_OFF, WM_KEYDOWN, VK_UP, 0 );
                     }
                     else if ( iDelta > 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_OFF, WM_KEYDOWN, VK_DOWN, 0 );
                     }
                     break;
                  }
               }
               break;
            }
            case ID_SPIN_CFG_VVSTAT:
            {
               switch ( pnmhdr->code )
               {
                  case UDN_DELTAPOS:
                  {
                     const NMUPDOWN* pUpDown = reinterpret_cast<NMUPDOWN*>(lParam);
                     const int iDelta = pUpDown->iDelta;
                     if ( iDelta < 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_VVSTAT, WM_KEYDOWN, VK_UP, 0 );
                     }
                     else if ( iDelta > 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_VVSTAT, WM_KEYDOWN, VK_DOWN, 0 );
                     }
                     break;
                  }
               }
               break;
            }
            case ID_SPIN_CFG_PPSTAT:
            {
               switch ( pnmhdr->code )
               {
                  case UDN_DELTAPOS:
                  {
                     const NMUPDOWN* pUpDown = reinterpret_cast<NMUPDOWN*>(lParam);
                     const int iDelta = pUpDown->iDelta;
                     if ( iDelta < 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_PPSTAT, WM_KEYDOWN, VK_UP, 0 );
                     }
                     else if ( iDelta > 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_PPSTAT, WM_KEYDOWN, VK_DOWN, 0 );
                     }
                     break;
                  }
               }
               break;
            }
            case ID_SPIN_CFG_OFFSTAT:
            {
               switch ( pnmhdr->code )
               {
                  case UDN_DELTAPOS:
                  {
                     const NMUPDOWN* pUpDown = reinterpret_cast<NMUPDOWN*>(lParam);
                     const int iDelta = pUpDown->iDelta;
                     if ( iDelta < 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_OFFSTAT, WM_KEYDOWN, VK_UP, 0 );
                     }
                     else if ( iDelta > 0 )
                     {
                        SendDlgItemMessage( hwnd, ID_EDIT_CFG_OFFSTAT, WM_KEYDOWN, VK_DOWN, 0 );
                     }
                     break;
                  }
               }
               break;
            }
         }

         break;
      }

      case WM_COMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         const WORD wCode = HIWORD(wParam);
         switch ( wCmd )
         {
            case IDOK:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     double temp_LL = LL;
                     {
                        const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_LL );
                        winassert( hwndEdit );

                        char buffer[80+1] = "";
                        GetWindowText( hwndEdit, buffer, sizeof(buffer) );
                        temp_LL = StringToFloat( buffer, precision_LL, min_LL, max_LL );

                        if ( ! IsValidFor_LL(temp_LL) )
                        {
                           SetFocus( hwndEdit );
                           BeepError();
                           return TRUE;
                        }
                     }

                     double temp_bb = bb;
                     {
                        const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_BB );
                        winassert( hwndEdit );

                        char buffer[80+1] = "";
                        GetWindowText( hwndEdit, buffer, sizeof(buffer) );
                        temp_bb = StringToFloat( buffer, precision_bb, min_bb, max_bb );

                        if ( ! IsValidFor_bb(temp_bb) )
                        {
                           SetFocus( hwndEdit );
                           BeepError();
                           return TRUE;
                        }
                     }

                     double temp_cc = cc;
                     {
                        const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_CC );
                        winassert( hwndEdit );

                        char buffer[80+1] = "";
                        GetWindowText( hwndEdit, buffer, sizeof(buffer) );
                        temp_cc = StringToFloat( buffer, precision_cc, min_cc, max_cc );

                        if ( ! IsValidFor_cc(temp_cc) )
                        {
                           SetFocus( hwndEdit );
                           BeepError();
                           return TRUE;
                        }
                     }

                     double temp_vv = vv;
                     {
                        const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_VV );
                        winassert( hwndEdit );

                        char buffer[80+1] = "";
                        GetWindowText( hwndEdit, buffer, sizeof(buffer) );
                        temp_vv = StringToFloat( buffer, precision_vv, min_vv, max_vv );

                        if ( ! IsValidFor_vv(temp_vv) )
                        {
                           SetFocus( hwndEdit );
                           BeepError();
                           return TRUE;
                        }
                     }

                     double temp_pp = pp;
                     {
                        const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_PP );
                        winassert( hwndEdit );

                        char buffer[80+1] = "";
                        GetWindowText( hwndEdit, buffer, sizeof(buffer) );
                        temp_pp = StringToFloat( buffer, precision_pp, min_pp, max_pp );

                        if ( ! IsValidFor_pp(temp_pp) )
                        {
                           SetFocus( hwndEdit );
                           BeepError();
                           return TRUE;
                        }
                     }

                     double temp_off = off;
                     {
                        const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_OFF );
                        winassert( hwndEdit );

                        char buffer[80+1] = "";
                        GetWindowText( hwndEdit, buffer, sizeof(buffer) );
                        temp_off = StringToFloat( buffer, precision_off, min_off, max_off );

                        if ( ! IsValidFor_off(temp_off) )
                        {
                           SetFocus( hwndEdit );
                           BeepError();
                           return TRUE;
                        }
                     }

                     double temp_vvstat = vvstat;
                     {
                        const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_VVSTAT );
                        winassert( hwndEdit );

                        char buffer[80+1] = "";
                        GetWindowText( hwndEdit, buffer, sizeof(buffer) );
                        temp_vvstat = StringToFloat( buffer, precision_vv, min_vv, max_vv );

                        if ( ! IsValidFor_vv(temp_vvstat) )
                        {
                           SetFocus( hwndEdit );
                           BeepError();
                           return TRUE;
                        }
                     }

                     double temp_ppstat = ppstat;
                     {
                        const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_PPSTAT );
                        winassert( hwndEdit );

                        char buffer[80+1] = "";
                        GetWindowText( hwndEdit, buffer, sizeof(buffer) );
                        temp_ppstat = StringToFloat( buffer, precision_pp, min_pp, max_pp );

                        if ( ! IsValidFor_pp(temp_ppstat) )
                        {
                           SetFocus( hwndEdit );
                           BeepError();
                           return TRUE;
                        }
                     }

                     double temp_offstat = offstat;
                     {
                        const HWND hwndEdit = GetDlgItem( hwnd, ID_EDIT_CFG_OFFSTAT );
                        winassert( hwndEdit );

                        char buffer[80+1] = "";
                        GetWindowText( hwndEdit, buffer, sizeof(buffer) );
                        temp_offstat = StringToFloat( buffer, precision_off, min_off, max_off );

                        if ( ! IsValidFor_off(temp_offstat) )
                        {
                           SetFocus( hwndEdit );
                           BeepError();
                           return TRUE;
                        }
                     }

                     LL = temp_LL;
                     bb = temp_bb;
                     cc = temp_cc;
                     vv = temp_vv;
                     pp = temp_pp;
                     off = temp_off;
                     vvstat = temp_vvstat;
                     ppstat = temp_ppstat;
                     offstat = temp_offstat;

                     SaveConfigFile();
                     EndDialog( hwnd, wCmd );
                     return TRUE;
                  }
               }
               return FALSE;
            }

            case IDCANCEL:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     EndDialog( hwnd, wCmd );
                     return TRUE;
                  }
               }
               return FALSE;
            }
         }
         return FALSE;
      }
      case WM_SYSCOMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         switch (wCmd)
         {
            case SC_CLOSE:
            {
               return TRUE;
            }
         }
         return FALSE;
      }
   }

   return FALSE;
}

static bool Configure( HWND hwndParent )
{
   const INT_PTR rc = DialogBoxParam( hinst, MAKEINTRESOURCE(ID_DLG_CFG), hwndParent, ConfigureDlgProc, 0 );
   winassert( rc > 0 );
   return ( rc == IDOK );
}

//------------------------------------------------------------------

static char reportfilename[_MAX_PATH] = { 0 };

static bool SaveReportFile( HWND hwndOwner )
{
   char tempreportfilename[_MAX_PATH] = { 0 };
   sprintfsafe( tempreportfilename, sizeof(tempreportfilename), "%s%s", exepath, "$REPORT$.$$$" );

   char cwd[_MAX_PATH] = "";
   getcwd( cwd, sizeof(cwd) );
   OPENFILENAME ofn = { 0 };
   {
      char filters[80*1] = "";
      {
         int offset = 0;
         {
            offset += sprintfsafe( filters+offset, sizeof(filters)-offset, "%s (%s)%c%s%c", "RPT"    , "*.rpt"        , '\0', "*.rpt"        , '\0' );
         }
      }
      ofn.lStructSize = sizeof(ofn);
      ofn.lpstrFilter = filters;
      ofn.hwndOwner = hwndOwner;
      ofn.lpstrFile = reportfilename;
      ofn.nMaxFile = sizeof(reportfilename);
      ofn.lpstrTitle = "Save report to...";
      ofn.lpstrDefExt = "RPT";
      ofn.Flags = OFN_OVERWRITEPROMPT | OFN_HIDEREADONLY | OFN_NOCHANGEDIR;
   }
   if ( ! *ofn.lpstrFile )
   {
      ofn.lpstrInitialDir = cwd;
   }

   for (;;)
   {
      if ( ! GetSaveFileName( &ofn ) )
      {
         return false;
      }

      {
         if ( ! CopyFile( tempreportfilename, reportfilename, FALSE ) )
         {
            MsgOkError( "Error!", "Could not copy report to file\n\n%s", reportfilename );
            continue;
         }
         else
         {
            return true;
         }
      }
   }
}

//--------------------------------------------------------------------

static int MakeReport()
{
   char tempreportfilename[_MAX_PATH] = { 0 };
   sprintfsafe( tempreportfilename, sizeof(tempreportfilename), "%s%s", exepath, "$REPORT$.$$$" );

   FILE*const pf = fopen( tempreportfilename, "w" );
   if ( ! pf )
   {
      return 0;
   }

   char line[_MAX_PATH] = "";

   {
      stringblank( line );
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return 0;
      }
   }

   const int i = 0;

   {
      char buffer[_MAX_PATH] = "";
      if ( *RunVersion )
      {
         sprintfsafe( buffer, sizeof(buffer), "%s - AirBench %s (%s)", FANORBOX[i], RunVersion, DT[i] );
      }
      else
      {
         sprintfsafe( buffer, sizeof(buffer), "%s (%s)", FANORBOX[i], DT[i] );
      }
      if ( withPower[i] )
      {
         sprintfsafe( line, sizeof(line), "%*s%s", (80/2)-strlen(buffer)/2, "", buffer );
      }
      else
      {
         sprintfsafe( line, sizeof(line), "   %s", buffer );
      }
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return 0;
      }
   }

   {
      stringblank( line );
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return 0;
      }
   }

   {
      strcpyarray( line, "ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÂÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ" );
      if ( withPower[i] )
      {
        strcatarray( line, "ÂÄÄÄÄÄÄÄÄÄÄÄÄÄÄÂÄÄÄÄÄÄÄÄÄÄÄÄÄÂÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ" );
      }
      strcatarray( line, "¿" );
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return 0;
      }
   }

   {
      strcpyarray( line, "³      CFM      ³    Pressure    " );
      if ( withPower[i] )
      {
         strcatarray( line, "³    Volts     ³    Amps     ³     Watts     " );
      }
      strcatarray( line, "³" );
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return 0;
      }
   }

   {
      strcpyarray( line, "ÃÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÅÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ" );
      if ( withPower[i] )
      {
         strcatarray( line, "ÅÄÄÄÄÄÄÄÄÄÄÄÄÄÄÅÄÄÄÄÄÄÄÄÄÄÄÄÄÅÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ" );
      }
      strcatarray( line, "´" );
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return 0;
      }
   }

   {
      for ( int j = 0; j < IC[i]; ++j )
      {
         sprintfsafe( line, sizeof(line), "³ %13.3f ³ %14.4f ", CFM[i][j], PRESUR[i][j] );
         if ( withPower[i] )
         {
            sprintfsafecat( line, sizeof(line), "³ %12.2f ³ %11.2f ³ %13.3f ", VOLTS[i][j], AMPS[i][j], WATTS[i][j] );
         }
         sprintfsafecat( line, sizeof(line), "³" );
         if ( fprintf( pf, "%s\n", line ) < 0 )
         {
            fclose( pf );
            return 0;
         }
      }
   }

   {
      strcpyarray( line, "ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÁÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ" );
      if ( withPower[i] )
      {
         strcatarray( line, "ÁÄÄÄÄÄÄÄÄÄÄÄÄÄÄÁÄÄÄÄÄÄÄÄÄÄÄÄÄÁÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ" );
      }
      strcatarray( line, "Ù" );
      if ( fprintf( pf, "%s\n", line ) < 0 )
      {
         fclose( pf );
         return 0;
      }
   }

   if ( fclose( pf ) != 0 )
   {
      return 0;
   }

   return 1;
}

//------------------------------------------------------------------

static char* reportbuffer = 0;
static int reportlength = 0;

//------------------------------------------------------------------

static void ReadReportFile( void )
{
   char tempreportfilename[_MAX_PATH] = { 0 };
   sprintfsafe( tempreportfilename, sizeof(tempreportfilename), "%s%s", exepath, "$REPORT$.$$$" );

   {
      long long fullreportlength = FileSize( tempreportfilename );
      reportlength = ( fullreportlength <= INT_MAX ) ? static_cast<int>(fullreportlength) : 0;
   }

   if ( reportbuffer )
   {
      delete [] reportbuffer, reportbuffer = 0;
   }
   {
      const int size = reportlength + 1;
      reportbuffer = new char[size];
   }
   stringblank( reportbuffer );

   FILE*const stream = fopen( tempreportfilename, "rb" );
   if ( ! stream )
   {
      return;
   }

   fread( reportbuffer, reportlength, 1, stream );

   fclose( stream );

   reportbuffer[reportlength] = '\0';
}

static INT_PTR CALLBACK ShowReportDlgProc( HWND hwnd, UINT message, WPARAM wParam, LPARAM lParam )
{
   static int MinWindowWidth = 0;
   static int MinWindowHeight = 0;

   switch ( message )
   {
      case WM_INITDIALOG:
      {
         CenterWindow( hwnd );
         EnableDisableMenuItem( GetSystemMenu(hwnd,FALSE), SC_CLOSE, false );

         ReadReportFile();

         {
            const HWND hwndMLE = GetDlgItem( hwnd, ID_MLE_REPORT );
            winassert( hwndMLE );

            #if NEVER
            SetWindowFont( hwndMLE, GetStockFont(ANSI_FIXED_FONT), FALSE );
            #else
            SetWindowFont( hwndMLE, hfontFixed, FALSE );
            #endif

            Edit_LimitText( hwndMLE, 0 );

            SetWindowText( hwndMLE, reportbuffer );
         }

         {
            RECT rect = { 0 };
            {
               BOOL bSuccess = GetWindowRect( hwnd, &rect );
               winassert( bSuccess );
            }
            MinWindowWidth = rect.right - rect.left;
            MinWindowHeight = rect.bottom - rect.top;
         }

         return TRUE;
      }

      case WM_COMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         const WORD wCode = HIWORD(wParam);
         switch ( wCmd )
         {
            case IDCANCEL:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     EndDialog( hwnd, wCmd );
                     return TRUE;
                  }
               }
               return FALSE;
            }
            case IDOK:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     SaveReportFile( hwnd );
                     return TRUE;
                  }
               }
               return FALSE;
            }
            case ID_PB_PRINT:
            {
               switch ( wCode )
               {
                  case BN_CLICKED:
                  {
                     const int i = 0;
                     {
                        const HDC hdc = GetPrinterDC();
                        if ( hdc )
                        {
                           const char* p = 0;
                           {
                              p = strrchr( filename[i], '\\' );
                              if ( p )
                              {
                                 ++p;
                              }
                           }
                           if ( ! p )
                           {
                              p = filename[i];
                           }
                           TextToPrinter( hdc, reportbuffer, p );
                           DeleteDC( hdc );
                        }
                     }
                     return TRUE;
                  }
               }
               return FALSE;
            }
         }
         return FALSE;
      }

      case WM_SYSCOMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         switch (wCmd)
         {
            case SC_CLOSE:
            {
               return TRUE;
            }
         }
         return FALSE;
      }

      case WM_GETMINMAXINFO:
      {
         if ( MinWindowWidth && MinWindowHeight )
         {
            MINMAXINFO*const pinfo = reinterpret_cast<MINMAXINFO*>(lParam);
            {
               pinfo->ptMinTrackSize.x = MinWindowWidth;
               pinfo->ptMinTrackSize.y = MinWindowHeight;
            }
         }

         return 0;
      }

      case WM_SIZE:
      {
         {
            RECT rectClient = { 0 };
            {
               BOOL bSuccess = GetClientRect( hwnd, &rectClient );
               winassert( bSuccess );
            }
            {
               const HWND hwndChild = GetDlgItem( hwnd, IDCANCEL );
               RECT rect = { 0 };
               {
                  GetWindowRect( hwndChild, &rect );
                  MapWindowRect( HWND_DESKTOP, hwnd, &rect );
               }
               const LONG x = rect.left;
               const LONG y = ( rectClient.bottom - rectClient.top ) - ( rect.bottom - rect.top );
               const LONG cx = rect.right - rect.left;
               const LONG cy = rect.bottom - rect.top;
               const RECT rectRef = rect;
               const LONG yRef = y;
               MoveWindow( hwndChild, x, y, cx, cy, TRUE );
               {
                  const int aid[] =
                  {
                     ID_PB_PRINT,
                     IDOK,
                  };
                  {
                     for ( int i = 0; i < DIMENSION(aid); ++i )
                     {
                        const HWND hwndChild = GetDlgItem( hwnd, aid[i] );
                        RECT rect = { 0 };
                        {
                           GetWindowRect( hwndChild, &rect );
                           MapWindowRect( HWND_DESKTOP, hwnd, &rect );
                        }
                        const LONG x = rect.left;
                        const LONG y = yRef - ( rectRef.top - rect.top );
                        const LONG cx = rect.right - rect.left;
                        const LONG cy = rect.bottom - rect.top;
                        MoveWindow( hwndChild, x, y, cx, cy, TRUE );
                     }
                  }
               }
               {
                  const HWND hwndChild = GetDlgItem( hwnd, ID_MLE_REPORT );
                  RECT rect = { 0 };
                  {
                     GetWindowRect( hwndChild, &rect );
                     MapWindowRect( HWND_DESKTOP, hwnd, &rect );
                  }
                  const LONG x = rect.left;
                  const LONG y = rect.top;
                  const LONG cx = ( rectClient.right - rectClient.left ) - rect.left*2;
                  const LONG cy = yRef - ( rectRef.top - rect.bottom ) - y;
                  MoveWindow( hwndChild, x, y, cx, cy, TRUE );
               }
               {
                  const HWND hwndChild = GetDlgItem( hwnd, ID_BITMAP_CORNER );
                  RECT rect = { 0 };
                  {
                     GetWindowRect( hwndChild, &rect );
                     MapWindowRect( HWND_DESKTOP, hwnd, &rect );
                  }
                  const LONG x = rectClient.right - 16;
                  const LONG y = rectClient.bottom - 16;
                  const LONG cx = 18;
                  const LONG cy = 18;
                  MoveWindow( hwndChild, x, y, cx, cy, TRUE );
               }
            }
            InvalidateRect( hwnd, 0, TRUE );
         }
         return 0;
      }

   }

   return FALSE;
}

static void ShowReport( HWND hwndParent )
{
   const INT_PTR rc = DialogBoxParam( hinst, MAKEINTRESOURCE(ID_DLG_SHOWREPORT), hwndParent, ShowReportDlgProc, 0 );
   winassert( rc > 0 );
}

//------------------------------------------------------------------

static bool GetExportName( char filename[], unsigned long cbfilename )
{
   char cwd[_MAX_PATH] = "";
   getcwd( cwd, sizeof(cwd) );
   OPENFILENAME ofn = { 0 };
   {
      char filters[80*1] = "";
      {
         int offset = 0;
         {
            offset += sprintfsafe( filters+offset, sizeof(filters)-offset, "%s (%s)%c%s%c", "CSV"    , "*.csv"        , '\0', "*.csv"        , '\0' );
         }
      }
      ofn.lStructSize = sizeof(ofn);
      ofn.lpstrFilter = filters;
      ofn.hwndOwner = hwndMain;
      ofn.lpstrFile = filename;
      ofn.nMaxFile = cbfilename;
      ofn.lpstrTitle = "Export to...";
      ofn.lpstrDefExt = "CSV";
      ofn.Flags = OFN_OVERWRITEPROMPT | OFN_HIDEREADONLY | OFN_NOCHANGEDIR;
   }
   if ( ! *ofn.lpstrFile )
   {
      ofn.lpstrInitialDir = cwd;
   }

   for (;;)
   {
      if ( ! GetSaveFileName( &ofn ) )
      {
         return false;
      }

      {
         FILE*const pf = fopen( filename, "w" );
         if ( ! pf )
         {
            MsgOkError( "Error!", "Could not write to file\n\n%s", filename );
            continue;
         }
         fclose( pf );
      }

      return true;
   }
}

//--------------------------------------------------------------------

static LRESULT CALLBACK WndProc( HWND hwnd, UINT message, WPARAM wParam, LPARAM lParam )
{
   static bool bRunning = false;

   switch( message )
   {
      case WM_USER_RUN_STOPPED:
      {
         ActivateWindow( hwndMain );

         {
            const char text[] = "Clean up!\n\nReduce blower speed to mininum and turn blower off.";
            MsgOk( "Clean up!", text );
         }

         CloseSerialPort( handlePressure );
         CloseSerialPort( handleCFM );

         EnableDisableMenuItem( GetMenu(hwnd), IDM_OPEN, true );
         EnableDisableMenuItem( GetMenu(hwnd), IDM_RUN, true );
         EnableDisableMenuItem( GetMenu(hwnd), IDM_QUIT, true );
         EnableDisableMenuItem( GetSystemMenu(hwnd,FALSE), SC_CLOSE, true );
         EnableDisableMenuItem( GetMenu(hwnd), IDM_SCALE, true );
         EnableDisableMenuItem( GetMenu(hwnd), IDM_SETUP, true );
         DrawMenuBar( hwnd );
         bRunning = false;

         SaveFile();

         InvalidateRect( hwnd, 0, TRUE );

         return 0;
      }

      case WM_USER_EXIT:
      {
         if ( ! HandleUnsavedData() )
         {
            return 0;
         }
         DestroyWindow( hwnd );
         return 0;
      }

      case WM_PAINT:
      {
         PAINTSTRUCT ps = { 0 };
         const HDC hdc = BeginPaint( hwnd, &ps );

         if ( TYPE[0][0] != 'r' )
         {
            SIZE size = { 0 };
            {
               RECT rect = { 0 };
               GetClientRect( hwnd, &rect );
               size.cx = rect.right - rect.left;
               size.cy = rect.bottom - rect.top;
            }

            struct DrawGraphStruct s( false, false );

            DrawGraph( hdc, size, &s );
         }

         EndPaint( hwnd, &ps );

         return 0;
      }

      case WM_DROPFILES:
      {
         const HDROP hdrop = reinterpret_cast<HDROP>(wParam);
         if ( bRunning )
         {
            BeepError();
         }
         else
         {
            const UINT NumFiles = DragQueryFile( hdrop, 0xFFFFFFFF, 0, 0 );
            {
               for ( UINT IndexFile = 0; IndexFile < NumFiles; ++IndexFile )
               {
                  char newfilename[sizeof(filename)] = "";
                  {
                     DragQueryFile( hdrop, IndexFile, newfilename, sizeof(newfilename) );
                  }
                  const char* ext = 0;
                  {
                     if ( strlen( newfilename ) >= 4 )
                     {
                        ext = newfilename + strlen(newfilename) - 4;
                     }
                  }
                  if ( ( stricmp( ext, ".FAN" ) != 0 ) && ( stricmp( ext, ".IMP" ) != 0 ) )
                  {
                     BeepError();
                  }
                  else
                  {
                     int i = -1;
                     {
                        for ( int itemp = 1; itemp < MAXFILES; ++itemp )
                        {
                           if ( ! bUsed[itemp] )
                           {
                              i = itemp;
                              break;
                           }
                        }
                     }

                     if ( i < 1 )
                     {
                        BeepError();
                     }
                     else
                     {
                        ReadFile( i, newfilename );
                     }
                  }
               }
            }
            FixOverlayAndBestCurveMenus();
            InvalidateRect( hwnd, 0, TRUE );
         }
         DragFinish( hdrop );
         break;
      }

      case WM_COMMAND:
      {
         const WORD wCmd = LOWORD(wParam);

         if ( ( IDM_GPIBADDR_FIRST <= wCmd ) && ( wCmd <= IDM_GPIBADDR_LAST ) )
         {
            gpibaddr = static_cast<char>( wCmd - IDM_GPIBADDR_BASE );
            CheckMenuRadioItem( GetMenu(hwndMain), IDM_GPIBADDR_FIRST, IDM_GPIBADDR_LAST, IDM_GPIBADDR_BASE+gpibaddr, MF_BYCOMMAND );
            SaveGpibFile();
            return 0;
         }

         if ( ( IDM_PWRSUPPLY_FIRST <= wCmd ) && ( wCmd <= IDM_PWRSUPPLY_LAST ) )
         {
            gpibaddrpower = static_cast<char>( wCmd - IDM_PWRSUPPLY_BASE );
            CheckMenuRadioItem( GetMenu(hwndMain), IDM_PWRSUPPLY_FIRST, IDM_PWRSUPPLY_LAST, IDM_PWRSUPPLY_BASE+gpibaddrpower, MF_BYCOMMAND );
            SaveGpibFile();
            return 0;
         }

         switch ( wCmd )
         {
            case IDM_OPEN:
            {
               const int i = 0;

               char buffer[sizeof(filename[i])] = "";
               strcpyarray( buffer, filename[i] );

               char cwd[_MAX_PATH] = "";
               getcwd( cwd, sizeof(cwd) );
               OPENFILENAME ofn = { 0 };
               {
                  char filters[80*1] = "";
                  int filter_index = 0;
                  {
                     int offset = 0;
                     {
                        offset += sprintfsafe( filters+offset, sizeof(filters)-offset, "%s (%s)%c%s%c", "FAN"    , "*.fan"        , '\0', "*.fan"        , '\0' );
                        offset += sprintfsafe( filters+offset, sizeof(filters)-offset, "%s (%s)%c%s%c", "IMP"    , "*.imp"        , '\0', "*.imp"        , '\0' );
                        // offset += sprintfsafe( filters+offset, sizeof(filters)-offset, "%s (%s)%c%s%c", "RAT"    , "*.rat"        , '\0', "*.rat"        , '\0' );
                     }
                     switch ( TYPE[i][0] )
                     {
                        case 'i':
                        {
                           filter_index = 2;
                           break;
                        }
                        case 'r':
                        {
                           // filter_index = 3;
                           break;
                        }
                        case 'f':
                        {
                           filter_index = 1;
                           break;
                        }
                     }
                  }
                  ofn.lStructSize = sizeof(ofn);
                  ofn.lpstrFilter = filters;
                  ofn.nFilterIndex = filter_index;
                  ofn.hwndOwner = hwnd;
                  ofn.lpstrFile = buffer;
                  ofn.nMaxFile = sizeof(buffer);
                  ofn.lpstrTitle = "Open...";
                  ofn.lpstrDefExt = 0;
                  ofn.Flags = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY | OFN_NOCHANGEDIR;
               }
               if ( ! *ofn.lpstrFile )
               {
                  ofn.lpstrInitialDir = cwd;
               }

               if ( ! GetOpenFileName( &ofn ) )
               {
                  break;
               }

               if ( ! HandleUnsavedData() )
               {
                  return 0;
               }

               ReadFile( i, buffer );
               UpdateWindowTitle();
               bUnsavedData = false;

               FixOverlayAndBestCurveMenus();

               InvalidateRect( hwnd, 0, TRUE );

               return 0;
            }

            case IDM_RUN:
            {
               const int i = 0;

               if ( ! gpib.isinit() )
               {
                  gpib.init();
                  if ( gpib.Error() )
                  {
                     MsgOkError( "GPIB Error!", "Could not initialize GPIB.\n\nTests cannot be run." );
                     return TRUE;
                  }
               }

               if ( AbType != ABTYPE_001 )
               {
                  if ( ( portPressure < 1 ) || ( portCFM < 1 ) )
                  {
                     if ( ! SetupSerial( hwnd ) )
                     {
                        return 0;
                     }
                  }
                  if ( ! DEMO )
                  {
                     handlePressure = SetupSerialPort( aPorts[portPressure] );
                     if ( handlePressure == BADHANDLE )
                     {
                        CloseSerialPort( handlePressure );
                        CloseSerialPort( handleCFM );
                        return 0;
                     }
                  }
                  if ( ! DEMO )
                  {
                     handleCFM = SetupSerialPort( aPorts[portCFM] );
                     if ( handlePressure == BADHANDLE )
                     {
                        CloseSerialPort( handlePressure );
                        CloseSerialPort( handleCFM );
                        return 0;
                     }
                  }
               }

               if ( ! HandleUnsavedData() )
               {
                  CloseSerialPort( handlePressure );
                  CloseSerialPort( handleCFM );
                  return 0;
               }

               if ( AbType == ABTYPE_001 )
               {
                  if ( ! IsConfigured() )
                  {
                     Configure( hwnd );
                  }
                  if ( ! IsConfigured() )
                  {
                     CloseSerialPort( handlePressure );
                     CloseSerialPort( handleCFM );
                     return 0;
                  }
               }

               if ( ! Prepare( hwnd ) )
               {
                  CloseSerialPort( handlePressure );
                  CloseSerialPort( handleCFM );
                  return 0;
               }
               Mutex.Request();
               bUsed[i] = false;
               IC[i] = 0;
               withPower[i] = !!gpibaddrpower;
               Calculate();
               stringblank( DT[i] );
               Mutex.Release();
               bUnsavedData = ( TYPE[0][0] != 'r' );
               strcpyarray( RunVersion, VERSION );
               InvalidateRect( hwnd, 0, TRUE );
               FixOverlayAndBestCurveMenus();

               {
                  bool bDone = false;
                  while ( ! bDone )
                  {
                     int rc = IDNO;
                     if ( TYPE[0][0] != 'r' )
                     {
                        rc = MsgYesNoCancelQuery( "Save new data?",
                              "Do you want to save the results for the NEW test to a file?" );
                     }
                     if ( MsgIsYes(rc) )
                     {
                        bSaveFile = GetSaveName();
                        if ( bSaveFile )
                        {
                           bSaveFileToLan = GetLanName( hinst, hwnd, filename[0], LAN, lanfilename, sizeof(lanfilename) );
                        }
                        bDone = bSaveFile;
                        UpdateWindowTitle();
                     }
                     else if ( MsgIsNo(rc) )
                     {
                        bSaveFile = false;
                        // {
                        //    char* p = strrchr( filename[i], '\\' );
                        //    if ( p )
                        //    {
                        //       ++p;
                        //    }
                        //    else
                        //    {
                        //       p = filename[i];
                        //    }
                        //    *p = '\0';
                        //    strcatarray( filename[i], "*.*" );
                        // }
                        stringblank( filename[i] );
                        bDone = true;
                        UpdateWindowTitle();
                     }
                     else
                     {
                        UpdateWindowTitle();
                        CloseSerialPort( handlePressure );
                        CloseSerialPort( handleCFM );
                        return 0;
                     }
                  }
               }

               if ( hdcAutoPrint )
               {
                  DeleteDC( hdcAutoPrint );
                  hdcAutoPrint = 0;
               }
               {
                  bool bDone = false;
                  while ( ! bDone )
                  {
                     int rc = IDNO;
                     if ( TYPE[0][0] != 'r' )
                     {
                        rc = MsgYesNoCancel( "Print?", "Would you like an automatic printout when the test is completed?" );
                     }
                     if ( MsgIsYes( rc ) )
                     {
                        if ( Names( hwnd ) )
                        {
                           InvalidateRect( hwnd, 0, TRUE );
                           hdcAutoPrint = GetPrinterDC();
                           if ( hdcAutoPrint )
                           {
                              bDone = true;
                           }
                        }
                     }
                     else if ( MsgIsNo( rc ) )
                     {
                        bDone = true;
                     }
                     else
                     {
                        CloseSerialPort( handlePressure );
                        CloseSerialPort( handleCFM );
                        return 0;
                     }
                  }
               }

               Mutex.Request();
               bUsed[i] = true;
               {
                  const time_t t = time(0);
                  strftime( DT[i], sizeof(DT[i]), "%m-%d-%Y", localtime(&t) );
               }
               Mutex.Release();
               InvalidateRect( hwnd, 0, TRUE );
               FixOverlayAndBestCurveMenus();

               EnableDisableMenuItem( GetMenu(hwnd), IDM_OPEN, false );
               EnableDisableMenuItem( GetMenu(hwnd), IDM_RUN, false );
               EnableDisableMenuItem( GetMenu(hwnd), IDM_QUIT, false );
               EnableDisableMenuItem( GetSystemMenu(hwnd,FALSE), SC_CLOSE, false );
               EnableDisableMenuItem( GetMenu(hwnd), IDM_SCALE, false );
               EnableDisableMenuItem( GetMenu(hwnd), IDM_SETUP, false );
               DrawMenuBar( hwnd );
               bRunning = true;
               bUnsavedData = ( TYPE[0][0] != 'r' );

               Run( hwnd );

               return 0;
            }

            case IDM_PRINTGRAPH:
            {
               const int i = 0;

               if ( ! Names( hwnd ) )
               {
                  return 0;
               }

               InvalidateRect( hwnd, 0, TRUE );

               const HDC hdc = GetPrinterDC();
               if ( hdc )
               {
                  const char* p = 0;
                  {
                     p = strrchr( filename[i], '\\' );
                     if ( p )
                     {
                        ++p;
                     }
                  }
                  if ( ! p )
                  {
                     p = filename[i];
                  }
                  const char*const docname = *FIG ? FIG : ( *p ? p : "AIRBENCH" );

                  struct DrawGraphStruct s( true, true );
                  TurnHourglassOn();
                  DoPrint( hdc, DrawGraph, &s, docname );
                  TurnHourglassOff();
                  DeleteDC( hdc );
               }

               return 0;
            }

            case IDM_PRINT:
            {
               #if NEVER
               if ( bRunning )
               {
                  return TRUE;
               }
               #endif

               MakeReport();

               ShowReport( hwnd );

               return TRUE;
            }

            case IDM_EXPORT:
            {
               char exportfilename[_MAX_PATH] = "";
               if ( GetExportName( exportfilename, sizeof(exportfilename) ) )
               {
                  FILE* pf = fopen( exportfilename, "w" );
                  if ( pf )
                  {
                     const int i = 0;
                     {
                        WriteExcel( pf, "CFM" );
                        WriteExcel( pf, "Pressure" );
                        if ( withPower[i] )
                        {
                           WriteExcel( pf, "Volts" );
                           WriteExcel( pf, "Amps" );
                           WriteExcel( pf, "Watts" );
                        }
                        fprintf( pf, "\n" );
                     }
                     {
                        for ( int j = 0; j < IC[i]; ++j )
                        {
                           WriteExcel( pf, "%.3f", CFM[i][j] );
                           WriteExcel( pf, "%.4f", PRESUR[i][j] );
                           if ( withPower[i] )
                           {
                              WriteExcel( pf, "%.2f", VOLTS[i][j] );
                              WriteExcel( pf, "%.2f", AMPS[i][j] );
                              WriteExcel( pf, "%.3f", WATTS[i][j] );
                           }
                           fprintf( pf, "\n" );
                        }
                     }
                     fclose( pf );
                  }
               }
               return 0;
            }

            case IDM_QUIT:
            {
               SendMessage( hwnd, WM_USER_EXIT, 0, 0 );
               return 0;
            }

            case IDM_ADD:
            {
               Mutex.Request();
               int i = -1;
               {
                  for ( int itemp = 1; itemp < MAXFILES; ++itemp )
                  {
                     if ( ! bUsed[itemp] )
                     {
                        i = itemp;
                        break;
                     }
                  }
               }
               Mutex.Release();

               if ( i < 1 )
               {
                  MsgOkError( "Error!",
                        "Too many overlay files open; at least one must be closed before you open another." );
                  return 0;
               }

               // char buffer[sizeof(mostrecentoverlayfilename)] = "";
               // strcpyarray( buffer, mostrecentoverlayfilename );
               char buffer[_MAX_PATH] = "";

               char cwd[_MAX_PATH] = "";
               getcwd( cwd, sizeof(cwd) );
               OPENFILENAME ofn = { 0 };
               {
                  char filters[80*1] = "";
                  int filter_index = 0;
                  {
                     int offset = 0;
                     {
                        offset += sprintfsafe( filters+offset, sizeof(filters)-offset, "%s (%s)%c%s%c", "FAN"    , "*.fan"        , '\0', "*.fan"        , '\0' );
                        offset += sprintfsafe( filters+offset, sizeof(filters)-offset, "%s (%s)%c%s%c", "IMP"    , "*.imp"        , '\0', "*.imp"        , '\0' );
                        // offset += sprintfsafe( filters+offset, sizeof(filters)-offset, "%s (%s)%c%s%c", "RAT"    , "*.rat"        , '\0', "*.rat"        , '\0' );
                     }
                     switch ( TYPE[i][0] )
                     {
                        case 'i':
                        {
                           filter_index = 2;
                           break;
                        }
                        case 'r':
                        {
                           // filter_index = 3;
                           break;
                        }
                        case 'f':
                        {
                           filter_index = 1;
                           break;
                        }
                     }
                  }
                  ofn.lStructSize = sizeof(ofn);
                  ofn.lpstrFilter = filters;
                  ofn.nFilterIndex = filter_index;
                  ofn.hwndOwner = hwnd;
                  ofn.lpstrFile = buffer;
                  ofn.nMaxFile = sizeof(buffer);
                  ofn.lpstrTitle = "Overlay...";
                  ofn.lpstrDefExt = 0;
                  ofn.Flags = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY | OFN_NOCHANGEDIR;
               }
               if ( ! *ofn.lpstrFile )
               {
                  ofn.lpstrInitialDir = cwd;
               }

               if ( ! GetOpenFileName( &ofn ) )
               {
                  break;
               }

               ReadFile( i, buffer );

               FixOverlayAndBestCurveMenus();

               InvalidateRect( hwnd, 0, TRUE );

               return 0;
            }

            case IDM_DELETE:
            {
               Delete( hwnd );

               FixOverlayAndBestCurveMenus();

               return 0;
            }

            // case IDM_BESTFITCURVE:
            // {
            //    bBestFitCurve = ! bBestFitCurve;
            //
            //    FixOverlayAndBestCurveMenus();
            //
            //    InvalidateRect( hwnd, 0, TRUE );
            //
            //    return 0;
            // }

            case IDM_NAMES:
            {
               if ( ! Names( hwnd ) )
               {
                  return 0;
               }
               InvalidateRect( hwnd, 0, TRUE );
               return 0;
            }

            case IDM_SCALE:
            {
               if ( ! Scale( hwnd ) )
               {
                  return 0;
               }
               CalculateScaleStuff();
               InvalidateRect( hwnd, 0, TRUE );
               return 0;
            }

            case IDM_CLIPBOARD:
            case IDM_SAVEFILE:
            {
               const int i = 0;

               if ( ! Names( hwnd ) )
               {
                  return 0;
               }

               InvalidateRect( hwnd, 0, TRUE );

               const char appname[] = "AIRBENCH";
               const char* p = 0;
               {
                  {
                     p = strrchr( filename[i], '\\' );
                     if ( p )
                     {
                        ++p;
                     }
                  }
                  if ( ! p )
                  {
                     p = filename[i];
                  }
               }
               const char*const picturename = *FIG ? FIG : ( ( p && *p ) ? p : "AIRBENCH" );

               SIZE size = { 0 };
               {
                  RECT rect = { 0 };
                  GetClientRect( hwnd, &rect );
                  size.cx = rect.right - rect.left;
                  size.cy = rect.bottom - rect.top;
               }
               DrawGraphStruct s( true, false );

               switch ( wCmd )
               {
                  case IDM_CLIPBOARD:
                  {
                     TurnHourglassOn();
                     CopyToClipboard( appname, picturename, hwnd, size, DrawGraph, &s );
                     TurnHourglassOff();
                     break;
                  }
                  default:
                  {
                     SaveToGraphicsFile( appname, picturename, hwnd, size, DrawGraph, &s );
                     break;
                  }
               }
               return 0;
            }

            case IDM_FONT_BOLD:
            {
               bBold = ! bBold;
               CheckUncheckMenuItem( GetMenu(hwnd), wCmd, bBold );
               InvalidateRect( hwnd, 0, TRUE );
               return 0;
            }
            case IDM_FONT_ITALIC:
            {
               bItalic = ! bItalic;
               CheckUncheckMenuItem( GetMenu(hwnd), wCmd, bItalic );
               InvalidateRect( hwnd, 0, TRUE );
               return 0;
            }
            case IDM_FONT_UP:
            {
               ++fontsize;
               FixFontSizeMenuItems( hwnd );
               InvalidateRect( hwnd, 0, TRUE );
               return 0;
            }
            case IDM_FONT_DOWN:
            {
               --fontsize;
               LowerBound( fontsize, 1 );
               FixFontSizeMenuItems( hwnd );
               InvalidateRect( hwnd, 0, TRUE );
               return 0;
            }
            case IDM_FONT_ARIAL:
            {
               strcpyarray( fontname, "Arial" );
               CheckMenuRadioItem( GetMenu(hwnd), IDM_FONT_ARIAL, IDM_FONT_TIMESNEWROMAN, IDM_FONT_ARIAL, MF_BYCOMMAND );
               InvalidateRect( hwnd, 0, TRUE );
               return 0;
            }
            case IDM_FONT_COURIERNEW:
            {
               strcpyarray( fontname, "Courier New" );
               CheckMenuRadioItem( GetMenu(hwnd), IDM_FONT_ARIAL, IDM_FONT_TIMESNEWROMAN, IDM_FONT_COURIERNEW, MF_BYCOMMAND );
               InvalidateRect( hwnd, 0, TRUE );
               return 0;
            }
            case IDM_FONT_TIMESNEWROMAN:
            {
               strcpyarray( fontname, "Times New Roman" );
               CheckMenuRadioItem( GetMenu(hwnd), IDM_FONT_ARIAL, IDM_FONT_TIMESNEWROMAN, IDM_FONT_TIMESNEWROMAN, MF_BYCOMMAND );
               InvalidateRect( hwnd, 0, TRUE );
               return 0;
            }

            case IDM_ABTYPE_001:
            case IDM_ABTYPE_002:
            {
               switch ( wCmd )
               {
                  case IDM_ABTYPE_001:
                  {
                     AbType = ABTYPE_001;
                     break;
                  }
                  case IDM_ABTYPE_002:
                  {
                     AbType = ABTYPE_002;
                     break;
                  }
               }
               WriteAbType();
               switch ( AbType )
               {
                  case ABTYPE_001:
                  {
                     CheckMenuRadioItem( GetMenu(hwndMain), IDM_ABTYPE_001, IDM_ABTYPE_002, IDM_ABTYPE_001, MF_BYCOMMAND );
                     break;
                  }
                  case ABTYPE_002:
                  {
                     CheckMenuRadioItem( GetMenu(hwndMain), IDM_ABTYPE_001, IDM_ABTYPE_002, IDM_ABTYPE_002, MF_BYCOMMAND );
                     break;
                  }
               }
               EnableDisableMenuItem( GetMenu(hwndMain), IDM_CFG, (AbType==ABTYPE_001) );
               EnableDisableMenuItem( GetMenu(hwndMain), IDM_SERIAL, (AbType!=ABTYPE_001) );
               if ( AbType == ABTYPE_001 )
               {
                  Configure( hwnd );
               }
               else
               {
                  SetupSerial( hwnd );
               }
               return 0;
            }

            case IDM_CFG:
            {
               Configure( hwnd );
               return 0;
            }

            case IDM_SERIAL:
            {
               SetupSerial( hwnd );
               return 0;
            }

         }
         break;
      }

      case WM_SYSCOMMAND:
      {
         const WORD wCmd = LOWORD(wParam);
         switch (wCmd)
         {
            case SC_CLOSE:
            {
               if ( bRunning )
               {
                  return TRUE;
               }
               SendMessage( hwnd, WM_USER_EXIT, 0, 0 );
               return 0;
            }
         }
         break;
      }

      case WM_QUERYENDSESSION:
      {
         if ( bRunning )
         {
            MsgOk( "Cancelled!", "Shutdown has been cancelled because a test is running!" );
            return FALSE;
         }
         return TRUE;
      }

      case WM_ENDSESSION:
      {
         const BOOL bEnding = wParam;
         if ( ! bEnding )
         {
            return 0;
         }
         SendMessage( hwnd, WM_USER_EXIT, 0, 0 );
         return 0;
      }

      case WM_DESTROY:
      {
         PostQuitMessage(0);
         return 0;
      }

   }
   return DefWindowProc( hwnd, message, wParam, lParam );
}

//--------------------------------------------------------------------

int WINAPI WinMain( HINSTANCE hinst, HINSTANCE hprev, LPSTR CmdLine, int CmdShow )
{
   timeBeginPeriod(1);
   bool bConsole = false;
   {
      for ( int i = 1; i <= (__argc-1); ++i )
      {
         if ( stricmp( __argv[i], "/CONSOLE" ) == 0 )
         {
            bConsole = true;
         }
         else if ( stricmp( __argv[i], "/DEMO" ) == 0 )
         {
            DEMO = true;
         }
         else if ( stricmp( __argv[i], "/NOINIT" ) == 0 )
         {
            NOINIT = true;
         }
         else
         {
            if ( ! pargv )
            {
               pargv = __argv[i];
            }
         }
      }
   }
   if ( DEMO )
   {
      srand( static_cast<int>(time(0)) );
   }
   int rc = 1;
   try
   {
      if ( bConsole )
      {
         SetupDebugConsole();
      }
      InitCommonControls();

      {
         GetModuleFileName( 0, exepath, sizeof(exepath) );
         {
            char* p = strrchr( exepath, '\\' );
            p = p ? (p+1) : exepath;
            *p = '\0';
         }
      }

      ::hinst = hinst;

      WNDCLASS wc = { 0 };
      {
         wc.lpszClassName = "AB";
         wc.hInstance = hinst;
         wc.lpfnWndProc = WndProc;
         wc.hbrBackground = GetStockBrush( WHITE_BRUSH );
         wc.style = CS_HREDRAW | CS_VREDRAW;
         wc.hIcon = LoadIcon( hinst, MAKEINTRESOURCE(IDM_MAIN) );
         wc.lpszMenuName = MAKEINTRESOURCE( IDM_MAIN );
         wc.hCursor = LoadCursor( 0, IDC_ARROW );
      }

      const ATOM atom = RegisterClass(&wc);

      hwndMain = CreateWindowEx
      (
         0,
         MAKEINTRESOURCE(atom),
         "AB",
         WS_OVERLAPPEDWINDOW,
         CW_USEDEFAULT, CW_USEDEFAULT, CW_USEDEFAULT, CW_USEDEFAULT,
         0,
         0,
         hinst,
         0
      );
      winassert( hwndMain );
      UpdateWindowTitle();

      const HACCEL haccel = LoadAccelerators( hinst, MAKEINTRESOURCE(IDM_MAIN) );
      winassert( haccel );

      {
         HDC hdc = GetWindowDC( hwndMain );
         hfontFixed = CreateFont( hdc, "Lucida Console", 8 );
         ReleaseDC( hwndMain, hdc );
      }

      {
         const int i = 0;
         {
            TYPE[i][0] = 'i';
            TYPE[i][1] = '\0';

            VDC[i] = 12;

            RPM[i] = 9999;

            SMM[i] = 25;

            PWM[i] = -1;

            PulseTimeInterval[i] = DefaultPulseTimeInterval( TYPE[i][0] );
         }

         if ( pargv )
         {
            char tmpfilename[sizeof(filename[0])] = "";
            strcpyarray( tmpfilename, pargv );
            {
               char newfilename[sizeof(filename[0])] = "";
               char* pFilePart = 0;
               if ( ! GetFullPathName( tmpfilename, sizeof(newfilename), newfilename, &pFilePart ) )
               {
                  MsgOkError( "Error!", "Could not find file\n\n%s", newfilename );
               }
               else
               {
                  ReadFile( i, newfilename );
                  UpdateWindowTitle();
                  InvalidateRect( hwndMain, 0, TRUE );
               }
            }
         }
      }

      DragAcceptFiles( hwndMain, true );

      FixOverlayAndBestCurveMenus();

      SendMessage( hwndMain, WM_COMMAND, IDM_FONT_ARIAL, 0 );
      FixFontSizeMenuItems( hwndMain );

      ReadAbType();
      switch ( AbType )
      {
         case ABTYPE_001:
         {
            CheckMenuRadioItem( GetMenu(hwndMain), IDM_ABTYPE_001, IDM_ABTYPE_002, IDM_ABTYPE_001, MF_BYCOMMAND );
            break;
         }
         case ABTYPE_002:
         {
            CheckMenuRadioItem( GetMenu(hwndMain), IDM_ABTYPE_001, IDM_ABTYPE_002, IDM_ABTYPE_002, MF_BYCOMMAND );
            break;
         }
      }
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_CFG, (AbType==ABTYPE_001) );
      EnableDisableMenuItem( GetMenu(hwndMain), IDM_SERIAL, (AbType!=ABTYPE_001) );

      gpib.init();
      if ( gpib.Error() )
      {
         MsgOkError( "GPIB Error!", "Could not initialize GPIB.\n\nTests cannot be run." );
      }

      {
         sprintfsafe( cfgfilename, sizeof(cfgfilename), "%s%s", exepath, "AB.CFG" );
         ReadConfigFile();
      }

      {
         sprintfsafe( gpibfilename, sizeof(gpibfilename), "%s%s", exepath, "$ABGPIB$.$$$" );
         ReadGpibFile();
      }
      CheckMenuRadioItem( GetMenu(hwndMain), IDM_GPIBADDR_FIRST, IDM_GPIBADDR_LAST, IDM_GPIBADDR_BASE+gpibaddr, MF_BYCOMMAND );
      CheckMenuRadioItem( GetMenu(hwndMain), IDM_PWRSUPPLY_FIRST, IDM_PWRSUPPLY_LAST, IDM_PWRSUPPLY_BASE+gpibaddrpower, MF_BYCOMMAND );

      {
         sprintfsafe( serialfilename, sizeof(serialfilename), "%s%s", exepath, "$ABCOMM$.$$$" );
         ReadSerialFile();
      }

      ShowWindow( hwndMain, SW_NORMAL );

      MSG msg;
      while( GetMessage( &msg, 0, 0, 0) )
      {
         if ( hwndDlgRun && IsDialogMessage( hwndDlgRun, &msg ) )
         {
            continue;
         }
         if ( TranslateAccelerator( hwndMain, haccel, &msg ) )
         {
            continue;
         }
         TranslateMessage( &msg );
         DispatchMessage( &msg );
      }
      rc = msg.wParam;

      DeleteFont( hfontFixed );
      hfontFixed = 0;

      if ( hdcAutoPrint )
      {
         DeleteDC( hdcAutoPrint );
         hdcAutoPrint = 0;
      }
   }
   catch( const char*const message )
   {
      printf( "%s\n", message );
      MsgException( "EXCEPTION", "%s\n\nReport this to your programmer!!!", message );
      throw;
   }
   catch( ... )
   {
      const char*const message = "UNKNOWN EXCEPTION";
      printf( "%s\n", message );
      MsgException( "EXCEPTION", "%s\n\nReport this to your programmer!!!", message );
      throw;
   }
   timeEndPeriod(1);
   return rc;
}

