#include "config.h"
#include "pt_cornell_1_2_1.h"

// graphics libraries
// SPI channel 1 connections to TFT
#include "tft_master.h"
#include "tft_gfx.h"
#include <stdlib.h>
#include <math.h>

#include <plib.h>
#include <stdio.h> /* For printf(). */



// frequency we're running at
#define	SYS_FREQ 40000000 


//Define fixed 16 notation for calculations
typedef signed int fix16 ;
#define multfix16(a,b) ((fix16)(((( signed long long)(a))*(( signed long long)(b)))>>16)) 
#define float2fix16(a) ((fix16)((a)*65536.0)) // 2^16
#define fix2float16(a) ((float)(a)/65536.0)
#define fix2int16(a)    ((int)((a)>>16))
#define int2fix16(a)    ((fix16)((a)<<16))
#define divfix16(a,b) ((fix16)((((signed long long)(a)<<16)/(b)))) 
#define sqrtfix16(a) (float2fix16(sqrt(fix2float16(a)))) 
#define absfix16(a) abs(a)

//PORTA 
#define EnablePullDownA(bits) CNPUACLR=bits; CNPDASET=bits;
// DAC ISR
// A-channel, 1x, active
#define DAC_config_chan_A 0b0011000000000000
// B-channel, 1x, active
#define DAC_config_chan_B 0b1011000000000000
#define Fs 8000.0
#define two32 4294967296.0 // 2^32 

#pragma config DEBUG = OFF

//****** All DAC and modulation variables ****//
volatile SpiChannel spiChn = SPI_CHANNEL2 ; // the SPI channel to use
// for 60 MHz PB clock use divide-by-3
volatile int spiClkDiv = 2 ; // 20 MHz DAC clock
volatile int DAC_A_data;
volatile int DAC_B_data;

// DDS sine table 
#define sine_table_size 256
#define rand_table_size 256
volatile int sin_table[sine_table_size];
volatile int rand_table[rand_table_size];
int desiredModulation = 0;
int modulation = 0;
volatile unsigned int phase_accum_main;
volatile unsigned int phase_incr_main = 261*two32/Fs;
volatile unsigned int phase_accum_error;
volatile unsigned int phase_incr_error = 800*two32/Fs;

#define phase_incr_main_C 261*two32/Fs
#define phase_incr_main_D 293*two32/Fs
#define phase_incr_main_E 329*two32/Fs
#define phase_incr_main_F 349*two32/Fs
#define phase_incr_main_G 392*two32/Fs


volatile int sin_table[sine_table_size];
volatile int rand_table[rand_table_size];
#define C_table_size 31
#define D_table_size 27
#define E_table_size 24
#define F_table_size 23
#define G_table_size 20

// sound buffer arrays to be filled with white noise for Karplus-Strong algorithm
volatile int C_table[C_table_size];
volatile int D_table[D_table_size];
volatile int E_table[E_table_size];
volatile int F_table[F_table_size];
volatile int G_table[G_table_size];

// constant int arrays
const int freqArray[] = {phase_incr_main_C, phase_incr_main_D, phase_incr_main_E, phase_incr_main_F, phase_incr_main_G};
const int sizeArray[] = {C_table_size, D_table_size, E_table_size, F_table_size, G_table_size};
const int OdeToJoy[] = {2,2,3,4,4,3,2,1,0,0,1,2,2,1,1,
                        2,2,3,4,4,3,2,1,0,0,1,2,1,0,0,
                        1,1,2,0,1,3,2,0,1,3,2,1,0,1,4,
                        2,2,3,4,4,3,2,1,0,0,1,2,1,0,0};
                       
// all game design variables
volatile int stringPattern;
volatile int currentGameTime;
volatile int strumVal;
volatile int score = 0;
volatile int correctNote;
volatile int scoreFactor = 1;
// add potentiometer to change difficulty level; set bounds from 30msec to 200msec over range
volatile int userErrorTolerance = 200;
volatile int totalNotesCorrect;

/**********************/
volatile int pluckIndexIn;
volatile int pluckIndexOut;
volatile int pluckCIndexIn;
volatile int pluckGIndexIn;
volatile int last_sample;
volatile int last_sample_in;
volatile int sample;
//volatile unsigned int time ;
volatile signed int string[256], last_tune_out, last_tune_in, lowpass_out ;
signed int tune, damping ;
/**********************/

// state declaration
enum GameState{menu = 0, Ode = 1};
enum GameState currentGameState = 0;


static struct pt pt_user_input, pt_anim, pt_game;
// === thread structures ============================================
// semaphores for controlling two threads
// for guarding the UART and for allowing stread blink control
static struct pt_sem control_t1, control_t2, send_sem ;
// thread control structs
// note that UART input and output are threads
static struct pt pt1, pt2, pt3, pt4, pt5, pt_input, pt_output, pt_DMA_output;
// turn threads 1 and 2 on/off and set thread timing
int cntl_blink = 1 ;
static int wait_t1 = 1000, wait_t3 = 500 ;// mSec
// control thread 4 rate
static int wait_t2 = 500 ;// microSec
static int run_t4 = 1 ;
// thread rate priorities
int t1_rate=3, t2_rate=3, t3_rate=3, t4_rate=0 ;
// system 1 second interval tick
int sys_time_seconds ;


char buffer[60];

// notes contain a current x and y position, the frequency type
typedef struct note_t {
    int x; // set x based on frequency, same x for F and G notes
    int y;
    int xprev;
    int yprev;
    int startTime;
    int endTime;
    int freq; // 0=C, 1=D, 2=E, 3=F, 4=G
    int playedCorrectly;
} note;

// notes in ode to joy - 61
#define n 61
note notes[n];
int noteIndex = 0; 
volatile int i;


// === Helper functions =================================================
char stringsToNote(int strings) {
    switch(strings) {
        case 0:
            return '_';
            break;
        case 1:
            return 'F';
            break;
        case 10:
            return 'E';
            break;
        case 101:
            return 'G';
            break;
        case 100:
            return 'D';
            break;
        case 1000:
            return 'C';
            break;
    }
}

// function to initialize all the original game pixels
void tft_initGamePixels(){
    tft_drawLine(50,0,50,319,ILI9340_WHITE);
    tft_drawLine(84,0,84,319,ILI9340_WHITE);
    tft_drawLine(119,0,119,319,ILI9340_WHITE);
    tft_drawLine(154,0,154,319,ILI9340_WHITE);
    tft_drawLine(190,0,190,319,ILI9340_WHITE);
    // note we must refill the circles during game when notes go over them - test FPS we should have at least 10
    tft_drawCircle(67, 20, 10, ILI9340_YELLOW);
    tft_drawCircle(102, 20, 10, ILI9340_RED);
    tft_drawCircle(137 , 20, 10, ILI9340_GREEN);
    tft_drawCircle(172, 20, 10, ILI9340_BLUE);
    tft_drawCircle(67, 20, 11, ILI9340_YELLOW);
    tft_drawCircle(102, 20, 11, ILI9340_RED);
    tft_drawCircle(137 , 20, 11, ILI9340_GREEN);
    tft_drawCircle(172, 20, 11, ILI9340_BLUE);
    
    tft_fillRoundRect(1,1,48,28,1,ILI9340_BLACK);
    tft_setCursor(1,1);
    tft_setTextColor(ILI9340_GREEN); tft_setTextSize(1);
    tft_writeString("SCORE");
    
    tft_setCursor(1,55);
    tft_setTextColor(ILI9340_YELLOW); tft_setTextSize(1);
    tft_writeString("SCORE");
    
    tft_setCursor(1,70);
    tft_setTextColor(ILI9340_YELLOW); tft_setTextSize(1);
    tft_writeString("FACTOR");
    
    tft_fillRoundRect(200,1,48,28,1,ILI9340_BLACK);
    tft_setCursor(200,1);
    tft_setTextColor(ILI9340_RED); tft_setTextSize(1);
    tft_writeString("TIME");
}

// helper function to redraw notes each animation cycle
void tft_redrawNotes(){
    tft_drawCircle(67, 20, 10, ILI9340_YELLOW);
    tft_drawCircle(102, 20, 10, ILI9340_RED);
    tft_drawCircle(137 , 20, 10, ILI9340_GREEN);
    tft_drawCircle(172, 20, 10, ILI9340_BLUE);
}

// helper function to draw note structures
void tft_drawNote(short xc, short yc, unsigned short color){
    tft_fillCircle(xc, yc, 8, color);
    if (color != ILI9340_BLACK && yc>20) tft_fillCircle(xc, yc, 2, ILI9340_WHITE);
}

void tft_drawX(){
    tft_drawLine(200, 200, 240, 100, ILI9340_RED);
    tft_drawLine(200, 100, 240, 200, ILI9340_RED);
}

void tft_deleteX(){
    tft_drawLine(200, 200, 240, 100, ILI9340_BLACK);
    tft_drawLine(200, 100, 240, 200, ILI9340_BLACK);
}

// helper function to take a frequency integer and convert to the string integer pattern
int freqToStrings (int freq) {
    switch(freq) {
        case 0:
            return 1000;
            break;
        case 1:
            return 100;
            break;
        case 2:
            return 10;
            break;
        case 3:
            return 1;
            break;
        case 4:
            return 101;
            break;
    }
}

// THE TIMER INTERRUPT THREAD TO PRODUCT GAME SOUND //
void __ISR(_TIMER_2_VECTOR, ipl2) TIMER2Handler(void)
{
    mT2ClearIntFlag();
    //if (PT_GET_TIME() < 1000) {
    phase_accum_error += phase_incr_error;
    phase_accum_main += phase_incr_main;
    DAC_A_data = sin_table[phase_accum_main>>24];
    //}

    // change from if played correctly to if start time and end time once input is given
    if ((notes[noteIndex].startTime < currentGameTime) && (modulation < 400) && 
            (notes[noteIndex].endTime > currentGameTime)) {
      // start modulation from 0 
      modulation += 1; 
    }
    else if ((notes[noteIndex].endTime < currentGameTime) && modulation > 0) {
      modulation -= 1; 
    }

    DAC_A_data *= (modulation);
    DAC_A_data = DAC_A_data>>12;

    // case statements for plucking noise dependent on frequency value

    if (notes[noteIndex].freq == 0) {
      DAC_B_data = (C_table[pluckIndexIn]>>16);  // sample out
      lowpass_out = multfix16(damping, ((C_table[pluckIndexIn]) + (C_table[pluckIndexOut]))>>1) ;
      C_table[pluckIndexIn] = multfix16(tune,(lowpass_out - last_tune_out)) + last_tune_in ;
    // all-pass state vars
      last_tune_out = C_table[pluckIndexIn];
      last_tune_in = lowpass_out;
    }

    else if (notes[noteIndex].freq == 1) {
      DAC_B_data = (D_table[pluckIndexIn]>>16);  // sample out
      lowpass_out = multfix16(damping, (D_table[pluckIndexIn] + D_table[pluckIndexOut])>>1) ;
      D_table[pluckIndexIn] = multfix16(tune,(lowpass_out - last_tune_out)) + last_tune_in ;
    // all-pass state vars
      last_tune_out = D_table[pluckIndexIn];
      last_tune_in = lowpass_out;
    }

    else if (notes[noteIndex].freq == 2) {
      DAC_B_data = (E_table[pluckIndexIn]>>16);  // sample out
      lowpass_out = multfix16(damping, ((E_table[pluckIndexIn]) + (E_table[pluckIndexOut]))>>1) ;
      E_table[pluckIndexIn] = multfix16(tune,(lowpass_out - last_tune_out)) + last_tune_in ;
    // all-pass state vars
      last_tune_out = E_table[pluckIndexIn];
      last_tune_in = lowpass_out;
    }
    
    else if (notes[noteIndex].freq == 3) {
      DAC_B_data = (F_table[pluckIndexIn]>>16);  // sample out
      lowpass_out = multfix16(damping, ((F_table[pluckIndexIn]) + (F_table[pluckIndexOut]))>>1) ;
      F_table[pluckIndexIn] = multfix16(tune,(lowpass_out - last_tune_out)) + last_tune_in ;
    // all-pass state vars
      last_tune_out = F_table[pluckIndexIn];
      last_tune_in = lowpass_out;
    }
    else if (notes[noteIndex].freq == 4) {
      DAC_B_data = (G_table[pluckIndexIn]>>16);  // sample out
      lowpass_out = multfix16(damping, ((G_table[pluckIndexIn]) + (G_table[pluckIndexOut]))>>1) ;
      G_table[pluckIndexIn] = multfix16(tune,(lowpass_out - last_tune_out)) + last_tune_in ;
    // all-pass state vars
      last_tune_out = G_table[pluckIndexIn];
      last_tune_in = lowpass_out;
    }
    
    if (notes[noteIndex].startTime < currentGameTime && (notes[noteIndex].playedCorrectly)) {
        pluckIndexIn = (pluckIndexIn + 1) % sizeArray[notes[noteIndex].freq];
        pluckIndexOut = (pluckIndexOut + 1) % sizeArray[notes[noteIndex].freq];
    }
    
    if ((!notes[noteIndex].playedCorrectly) && (noteIndex<n-1) && ((notes[noteIndex].startTime + userErrorTolerance)<currentGameTime)) {
        //DAC_B_data = DAC_B_data + (rand() & 0x00ff) - 128;
        DAC_B_data = sin_table[phase_accum_error>>24];
        DAC_B_data = DAC_B_data >> 8;
    }

    // prevent any overflow from DAC_B_data
    if (DAC_B_data>4095) DAC_B_data = 4095;

    
    // write to DAC_A
    mPORTBClearBits(BIT_4);
    WriteSPI2(DAC_config_chan_A | (DAC_A_data + 2048));
    while (SPI2STATbits.SPIBUSY); //wait 
    mPORTBSetBits(BIT_4); // end transaction

    // write to DAC_B
    mPORTBClearBits(BIT_4);
    WriteSPI2(DAC_config_chan_B | (DAC_B_data));
    while (SPI2STATbits.SPIBUSY); //wait 
    mPORTBSetBits(BIT_4); // end transaction

}

// === Thread 3 ======================================================
// The serial interface
static char cmd[16];
char buff[1];
static int value;

static PT_THREAD (protothread3(struct pt *pt))
{
    PT_BEGIN(pt);
      while(1) {
            
            //sprintf(PT_send_buffer,"cmd>");
            //// by spawning a print thread
        //    mPORTAClearBits(BIT_0 );	//Clear bits to ensure light is off.
            PT_SPAWN(pt, &pt_input, PT_GetSerialBuffer(&pt_input) );
//            sscanf(PT_term_buffer, "%s %d", cmd, &value);
            	int dec = 0, i, j, len;
            len = strlen(PT_term_buffer);
            if(len > 3){
                for(i=0; i<len; i++){
                    dec = dec * 10 + ( PT_term_buffer[i] - '0' );
                }
                // only update stringPattern when there is a non-zero transmission
                if (dec>0) stringPattern = dec;
                //if(dec < 50) {
                   mPORTAToggleBits(BIT_0 ); //Clear bits to ensure light is off.
                // initialize strumVal to 1 whenever there is a received transmission
                strumVal = 1;
            }
            //};

//            PT_SPAWN(pt, &pt_DMA_output, PutSerialBuffer(&pt_DMA_output) );
            PT_YIELD_TIME_msec(25);
            // never exit while
      } // END WHILE(1)
  PT_END(pt);
} // thread 3


// === Animation Thread =============================================

static PT_THREAD (protothread_anim(struct pt *pt))
{
  PT_BEGIN(pt);
          while(1) {
            int begin_time = PT_GET_TIME();

            for (i = 0; i<4; i++){
                notes[noteIndex+i].yprev = notes[noteIndex+i].y;
                notes[noteIndex+i].y = 20 - ((currentGameTime-notes[noteIndex+i].startTime)/10);
            }
            for (i = 0; i<4; i++){
                if (noteIndex+i<n-1) {
                    if (notes[noteIndex+i].freq == 4){
                        tft_drawNote(102,notes[noteIndex+i].yprev,ILI9340_BLACK);
                        tft_drawNote(102,notes[noteIndex+i].y,ILI9340_RED);
                        tft_drawNote(notes[noteIndex+i].x,notes[noteIndex+i].yprev,ILI9340_BLACK);
                        tft_drawNote(notes[noteIndex+i].x,notes[noteIndex+i].y,ILI9340_BLUE);
                    }
                    else if (notes[noteIndex+i].freq == 3){
                        tft_drawNote(172,notes[noteIndex+i].yprev,ILI9340_BLACK);
                        tft_drawNote(172,notes[noteIndex+i].y,ILI9340_BLUE);
                    }
                    else if (notes[noteIndex+i].freq == 1){
                        tft_drawNote(102,notes[noteIndex+i].yprev,ILI9340_BLACK);
                        tft_drawNote(102,notes[noteIndex+i].y,ILI9340_RED);
                    }
                    else if (notes[noteIndex+i].freq == 0){
                        tft_drawNote(67,notes[noteIndex+i].yprev,ILI9340_BLACK);
                        tft_drawNote(67,notes[noteIndex+i].y,ILI9340_YELLOW);
                    }
                    else{
                        tft_drawNote(notes[noteIndex+i].x,notes[noteIndex+i].yprev,ILI9340_BLACK);
                        tft_drawNote(notes[noteIndex+i].x,notes[noteIndex+i].y,ILI9340_GREEN);
                    }
                }
            }
            if (noteIndex>=1) {
                tft_drawNote(notes[noteIndex-1].x,notes[noteIndex-1].yprev, ILI9340_BLACK);
                tft_drawNote(notes[noteIndex-1].x,notes[noteIndex-1].y, ILI9340_BLACK);
            }
            tft_redrawNotes();
            
            tft_fillRoundRect(1,25,48,14,1,ILI9340_BLACK);
            tft_setCursor(1,25);
            tft_setTextColor(ILI9340_GREEN); tft_setTextSize(1);
            sprintf(buffer,"%d",score);
            tft_writeString(buffer);
            
            tft_fillRoundRect(1,85,48,14,1,ILI9340_BLACK);
            tft_setCursor(1,85);
            tft_writeString("x");
            tft_setCursor(10,85);
            tft_setTextColor(ILI9340_YELLOW); tft_setTextSize(1);
            sprintf(buffer,"%d",scoreFactor);
            tft_writeString(buffer);
            
//            tft_fillRoundRect(1,150,48,14,1,ILI9340_BLACK);
//            tft_setCursor(1,150);
//            tft_setTextColor(ILI9340_YELLOW); tft_setTextSize(1);
//            sprintf(buffer,"%d",strumVal);
//            tft_writeString(buffer);
            
            // display the frequency of the current note
            tft_fillRoundRect(1,120,48,14,1,ILI9340_BLACK);
            tft_setCursor(1,120);
            tft_writeString("Note:");
            tft_setCursor(1, 140);
            char note[1];
            note[0] = stringsToNote(stringPattern);
            switch(note[0]){
                case 'C':
                    tft_setTextColor(ILI9340_YELLOW);
                    break;
                case 'D':
                    tft_setTextColor(ILI9340_RED);
                    break;
                case 'E':
                    tft_setTextColor(ILI9340_GREEN);
                    break;
                case 'F':
                    tft_setTextColor(ILI9340_BLUE);
                    break;
                case 'G':
                    tft_setTextColor(ILI9340_MAGENTA);
                    break;
                
            }
             tft_setTextSize(1);
            tft_fillRoundRect(1,140,48,14,1,ILI9340_BLACK);

            tft_writeString(note);
            
            tft_fillRoundRect(200,25,48,14,1,ILI9340_BLACK);
            tft_setCursor(200,25);
            tft_setTextColor(ILI9340_RED); tft_setTextSize(1);
            sprintf(buffer,"%d",currentGameTime>>10);
            tft_writeString(buffer);
//            
//            tft_fillRoundRect(1,200,48,14,1,ILI9340_BLACK);
//            tft_setCursor(1,200);
//            tft_setTextColor(ILI9340_YELLOW); tft_setTextSize(1);
//            sprintf(buffer,"%d",noteIndex);
//            tft_writeString(buffer);
            
            PT_YIELD_TIME_msec(62-(PT_GET_TIME()-begin_time)) ; // 15 hz constant frame rate
    }
  PT_END(pt);
} // end animation thread

static PT_THREAD (protothread_game(struct pt *pt))
{
  PT_BEGIN(pt);
          while(1) {
              currentGameTime = PT_GET_TIME();
              // set phase increment for current note to be played in ISR
              phase_incr_main = freqArray[notes[noteIndex].freq];
              if ((notes[noteIndex].startTime >= currentGameTime - userErrorTolerance) &&
                      (notes[noteIndex].startTime <= currentGameTime + userErrorTolerance)) {
//                  mPORTASetBits(BIT_0); // use LED for debugging
              }
//              else mPORTAClearBits(BIT_0);
                if (strumVal == 1) {//threhold) {
                  if ((notes[noteIndex].startTime >= currentGameTime - userErrorTolerance) &&
                      (notes[noteIndex].startTime <= currentGameTime + userErrorTolerance) && 
                      (stringPattern == freqToStrings(notes[noteIndex].freq))) {
                      // need to add in a if first not played correctly then set
                      // else it is a repeat note and incorrect!
                    strumVal = 0;
                    if (notes[noteIndex].playedCorrectly == 1) {
                        scoreFactor = 1;
//                        notes[noteIndex].playedCorrectly = 0;
                    }
                    else {
                        notes[noteIndex].playedCorrectly = 1;
                        score = score + 1*scoreFactor; 
                        if(stringsToNote(stringPattern) == 'G') score += scoreFactor; 
                        scoreFactor += 1;
                    }
                    if (scoreFactor > 30) {
                        scoreFactor = 30;
                    }
                  }
                  else {
                      strumVal = 0;
                      scoreFactor = 1; //GOOD score factor reset
                      score -= 2; // decrement score for any missed note
                      if(score < 0) score = 0;
                  }
                }
              
            if ((notes[noteIndex].startTime + userErrorTolerance < currentGameTime) && (!notes[noteIndex].playedCorrectly)) {
                scoreFactor = 1; 
              }        
                // increment note index unless the next note does not exist
            if ((notes[noteIndex].endTime < currentGameTime) && (notes[noteIndex].endTime != 0)) { 
              noteIndex = noteIndex + 1;
              last_tune_in = 0;
              last_tune_out = 0;
              pluckIndexIn = 1;
              pluckIndexOut = 2;
                // when we increment noteIndex we also have to reset the last freq_Table to be random
              switch (notes[noteIndex-1].freq) {
                  case 0: 
                      for (i = 0; i<C_table_size; i++) {
                        C_table[i] = rand_table[i]; // 0 to 4095 random number
                      }
                      break;
                  case 1:
                      for (i = 0; i<C_table_size; i++) {
                        D_table[i] = rand_table[i]; // 0 to 4095 random number
                      }
                      break;    
                  case 2: 
                      for (i = 0; i<C_table_size; i++) {
                        E_table[i] = rand_table[i]; // 0 to 4095 random number
                      }
                      break;
                  case 3:
                      for (i = 0; i<C_table_size; i++) {
                        F_table[i] = rand_table[i]; // 0 to 4095 random number
                      }
                      break;
                  case 4: 
                      for (i = 0; i<C_table_size; i++) {
                        G_table[i] = rand_table[i]; // 0 to 4095 random number
                      }
                      break;
              }
            }
              
              // if last note is played and current gametime is over 
              if ((noteIndex == n-1) && (notes[noteIndex].endTime < currentGameTime)) {
                  tft_fillRoundRect(1,1,240,320,1,ILI9340_BLACK);
                  tft_setCursor(20,20);
                  tft_setTextColor(ILI9340_RED); tft_setTextSize(2);
                  tft_writeString("GAME OVER");
                  tft_setCursor(20,60);
                  tft_setTextColor(ILI9340_YELLOW); tft_setTextSize(2);
                  tft_writeString("Final Score:");
                  tft_setCursor(20,100);
                  tft_setTextColor(ILI9340_GREEN); tft_setTextSize(2);
                  sprintf(buffer,"%d",score);
                  tft_writeString(buffer);
                  for (i=0;i<n-1;i++) {
                      if (notes[i].playedCorrectly) totalNotesCorrect++;
                  }
                  tft_setCursor(20,140);
                  tft_setTextColor(ILI9340_YELLOW); tft_setTextSize(2);
                  tft_writeString("Correct Notes:");
                  tft_setCursor(20,180);
                  tft_setTextColor(ILI9340_GREEN); tft_setTextSize(2);
                  sprintf(buffer,"%d",totalNotesCorrect);
                  tft_writeString(buffer);
                  tft_setCursor(60,180);
                  tft_setTextColor(ILI9340_GREEN); tft_setTextSize(2);
                  tft_writeString("out of");
                  tft_setCursor(160,180);
                  tft_setTextColor(ILI9340_GREEN); tft_setTextSize(2);
                  sprintf(buffer,"%d",n-1);
                  tft_writeString(buffer);
                  tft_setCursor(20,220);
                  tft_setTextColor(ILI9340_GREEN); tft_setTextSize(1);
                  tft_writeString("Press Reset to Restart Game");
                  while(1); // wait for player reset to restart game
              }
            PT_YIELD_TIME_msec(1) ; // yield for as little time as possible
        }
  PT_END(pt);
} // end game thread

// === Main  ======================================================
void main(void) {
    // timer2 at 40MHz for 5000 cycles is 8KHz
  OpenTimer2(T2_ON | T2_SOURCE_INT | T2_PS_1_1, 5000);  
    // set up timer with priority 1
  ConfigIntTimer2(T2_INT_ON | T2_INT_PRIOR_1);
  mT2ClearIntFlag(); // clear interrupt flag
  
  PPSOutput(2, RPB5, SDO2);
  // control CS for DAC 
  mPORTBSetPinsDigitalOut(BIT_4);
  mPORTBSetBits(BIT_4);
  //SPI setup
  SpiChnOpen(spiChn, SPI_OPEN_ON | SPI_OPEN_MODE16 | SPI_OPEN_MSTEN | SPI_OPEN_CKE_REV , 
          spiClkDiv);
  
  
  mPORTASetPinsDigitalIn(BIT_2 | BIT_3);
  EnablePullDownA(BIT_2 | BIT_3);
  
// === set up i/o port pin ===============
//  mPORTASetBits(BIT_0 | BIT_1 );	//Clear bits to ensure light is off.
  mPORTASetPinsDigitalIn(BIT_0 | BIT_1 );    //Set port as output
//  mPORTBSetBits(BIT_0 );	//Clear bits to ensure light is off.
  mPORTASetPinsDigitalOut(BIT_0 );    //Set port as output


//  ANSELA = 0; ANSELB = 0; 
//
//  initADC();
  
  // === config threads ==========
  // turns OFF UART support and debugger pin,  unless defines are set
  PT_setup();

  // === setup system wide interrupts  ========
  INTEnableSystemMultiVectoredInt();

  // init the threads
  PT_INIT(&pt_anim);
  PT_INIT(&pt_game);
  PT_INIT(&pt3);

  //initialize rand() function
  srand((unsigned) time(NULL));
  int i;
//  for (i = 0; i<sine_table_size; i++){
//      sin_table[i] = (int) rand() & 0x0fff;
//  }
  for (i = 0; i<sine_table_size; i++) {
      sin_table[i] = (int) (2047*sin((float)i*6.283/(float)(sine_table_size)));
  }

   for (i = 0; i<rand_table_size; i++) {
      //rand_table[i] = int2fix16(rand() & 0x0fff); // 0 to 4095 random number
      rand_table[i] = int2fix16(((rand() + rand() + rand() + rand())>>1) & 0x0fff); // 0 to 4095 random number

  }
  // initialize string tables
  for (i = 0; i<C_table_size; i++) {
      C_table[i] = rand_table[i]; // 0 to 4095 random number
  }
    for (i = 0; i<D_table_size; i++) {
      D_table[i] = rand_table[i]; // 0 to 4095 random number
  }
    for (i = 0; i<E_table_size; i++) {
      E_table[i] = rand_table[i]; // 0 to 4095 random number
  }
    for (i = 0; i<F_table_size; i++) {
      F_table[i] = rand_table[i]; // 0 to 4095 random number
  }
    for (i = 0; i<G_table_size; i++) {
      G_table[i] = rand_table[i]; // 0 to 4095 random number
  }

/**********************/
  pluckIndexOut= 2; // circular pointer 
  pluckIndexIn = 1; // circular pointer 
  last_tune_out = 0 ;
  last_tune_in = 0 ;
  tune = float2fix16(0.14) ; //tuning for acoustic guitar
  damping = float2fix16(1) ; // must be 0.5<damping<=1.0

/**********************/

// Ode to Joy song generation consisting of 60 notes
  for(i = 0; i<n-1; i++) {
    notes[i].startTime = 2000+i*833;
    notes[i].endTime = notes[i].startTime+800;
    notes[i].freq = i%4;
    notes[i].x = 67+(i%4)*35;
    notes[i].yprev = 340;
    notes[i].y = 340;
    notes[i].playedCorrectly = 0;
  }
  for (i = 0; i<15; i++) {
      notes[i].startTime = 2000+i*833;
      notes[i].endTime = notes[i].startTime+800;
  }
  notes[14].endTime = notes[14].startTime+1600;
  for (i = 15; i<30; i++) {
      notes[i].startTime = 2833+i*833;
      notes[i].endTime = notes[i].startTime+800;
  }
  notes[29].endTime = notes[29].startTime+1600;
  for (i=30;i<45;i++) {
      notes[i].startTime = 3666+i*833;
      notes[i].endTime = notes[i].startTime+800;
  }
  notes[44].endTime = notes[44].startTime+1600;
   for (i=45;i<60;i++) {
      notes[i].startTime = 4499+i*833;
      notes[i].endTime = notes[i].startTime+800;
  }
  notes[59].endTime = notes[59].startTime+1600;
  for(i = 0; i <n-1;i++) {
      notes[i].freq = OdeToJoy[i];
  }
  for (i = 0; i<n-1;i++) {
      notes[i].x = 67+(notes[i].freq)*35;
      if (notes[i].x > 172) notes[i].x = 172;
  }
  // init the display
  // NOTE that this init assumes SPI channel 1 connections
  tft_init_hw();
  tft_begin();
  tft_fillScreen(ILI9340_BLACK);
  //240x320 vertical display
  tft_setRotation(0); // Use tft_setRotation(0) for 240x320
  
  tft_initGamePixels();
  //tft_drawX();
  // round-robin scheduler for threads
     
  // init the optional rate scheduler
  PT_RATE_INIT();
  
  while (1){
    PT_SCHEDULE(protothread3(&pt3));
    PT_SCHEDULE(protothread_anim(&pt_anim));
    PT_SCHEDULE(protothread_game(&pt_game));
  }
}