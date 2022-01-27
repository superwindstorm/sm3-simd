// Copyright (c) 2022, superwindstorm <fengwd.hc@gmail.com>
// All rights reserved.
// Use of this source code is governed by a BSD 3-Clause
// license that can be found in the LICENSE file.

#include "textflag.h"

// SM3 block routine.
//
// No "function stitching" now.
// 
// The algorithm is detailed in GB/T 32905-2016

// FFt(x,y,z) = GGt(x,y,z) = Parity(x,y,z) for 0 <= t <= 15
// FFt(x,y,z) = Maj(x,y,z) for 15 <= t <= 63
// GGt(x,y,z) = Ch(x,y,z)  for 15 <= t <= 63
// 
// Wt = Mt; for 0 <= t <= 15
// Wt = P1(Wt-16 xor Wt-9 xor ROTL(Wt-3,15))
//          xor ROTL(Wi-13, 7) xor Wt-6 for 16 <= t <= 67
// W't = Wt xor Wt+4  for 0 <= t <= 63.
//
// a = V0
// b = V1
// c = V2
// d = V3
// e = V4
// f = V5
// g = V6
// h = V7
//
// for t = 0 to 63 {
//    SS1 = ROTL(ROTL(a,12) + E + ROTL(Tt, t mod 32), 7)
//    SS2 = SS1 xor ROTL(a,12) 
//    TT1 = FFt(a,b,c) + D + SS2 +W't
//    TT2 = GGt(e,f,g) + h + SS1 +Wt
//    d = c
//    c = ROTL(b,9)
//    b = a
//    a = TT1
//    h = g
//    g = ROTL(f,19)
//    f = e
//    e = P0(TT2)
// }
//
// V0 = a xor V0
// V1 = b xor V1
// V2 = c xor V2
// V3 = d xor V3
// V4 = e xor V4
// V5 = f xor V5
// V6 = g xor V6
// V7 = h xor V7

// Definitions for AVX2 version

// xorm (mem), reg
// Xor reg to mem using reg-mem xor and store
#define xorm(P1, P2) \
	XORL P2, P1; \
	MOVL P1, P2

#define XDWORD0 Y4
#define XDWORD1 Y5
#define XDWORD2 Y6
#define XDWORD3 Y7

#define XWORD0 X4
#define XWORD1 X5
#define XWORD2 X6
#define XWORD3 X7

#define XTMP0 Y0
#define XTMP1 Y1
#define XTMP2 Y2
#define XTMP3 Y3
#define XTMP4 Y8
#define XTMP5 Y11

#define XFER  Y9

#define BYTE_FLIP_MASK 	Y13 // mask to convert LE -> BE
#define X_BYTE_FLIP_MASK X13

#define NUM_BYTES DX
#define INP	DI

#define CTX SI // Beginning of digest in memory (a, b, c, ... , h)

#define a AX
#define b BX
#define c CX
#define d R8
#define e DX
#define f R9
#define g R10
#define h R11

#define old_h R11

#define TBL BP

#define SRND SI // SRND is same register as CTX

#define T1 R12

#define y0 R13
#define y1 R14
#define y2 R15
#define y3 DI

// Offsets
#define XFER_SIZE 2*2*68*4
#define INP_END_SIZE 8
#define INP_SIZE 8

#define _XFER 0
#define _INP_END _XFER + XFER_SIZE
#define _INP _INP_END + INP_END_SIZE
#define STACK_SIZE _INP + INP_SIZE


#define SM3_SCHED(XDWORD0, XDWORD1, XDWORD2, XDWORD3)\
	;                                       \ // ################################### Message Schedule ###########################
	VPALIGNR $8, XDWORD2, XDWORD3, XTMP0;   \ // XTMP0 = W[-6]
	VPALIGNR $12, XDWORD0, XDWORD1, XTMP1;  \ // XTMP1 = W[-13]
    VPSLLD   $7, XTMP1, XTMP2;              \
    VPSRLD   $(32-7), XTMP1, XTMP1;         \
    VPXOR    XTMP2, XTMP1, XTMP1;           \ // XTMP1 = (w[-13] <<< 7)
    VPXOR    XTMP1, XTMP0, XTMP0;           \ // XTMP0 = (w[-13] <<< 7) ^ w[-6]
    ;                                       \
	VPALIGNR $12, XDWORD1, XDWORD2, XTMP1;  \ // XTMP1 = W[-9]
    VPXOR   XDWORD0, XTMP1, XTMP1;          \ // XTMP1 = W[-9]^W[-16]
    ;                                       \
    VPSHUFD $0xA5, XDWORD3, XTMP2;          \ // XTMP2 = W[-3] {BBAA}
	VPSRLQ  $17, XTMP2, XTMP4;              \ // XTMP4 = W[-3] <<< 15 {xBxA}
    VPSHUFB shuff_00BA<>(SB), XTMP4, XTMP4; \ // XTMP4 = W[-3] <<< 15 {00BA}
    VPXOR   XTMP1, XTMP4, XTMP4;            \ // XTMP4 = W[-9]^W[-16] ^ (W[-3] <<< 15) {xxBA}
    VPSHUFD $0x50, XTMP4, XTMP4;            \ // XTMP4 = W[-9]^W[-16] ^ (W[-3] <<< 15) {BBAA}
    VPSRLQ  $17, XTMP4,XTMP2;               \ // {xBxA}
    VPSRLQ  $9, XTMP4,XTMP3;                \ // {xBxA}
    VPXOR   XTMP2, XTMP4, XTMP4;            \ //
    VPXOR   XTMP3, XTMP4, XTMP4;            \ // XTMP4 = p1 {xBxA}
    VPSHUFB shuff_00BA<>(SB), XTMP4, XTMP4; \ // XTMP4 = p1 {00BA}
    VPXOR   XTMP4, XTMP0, XTMP5;            \ // XTMP5 = {..., ..., W[1], W[0]}
    ;                                       \
    VPALIGNR $4, XDWORD3, XTMP5, XTMP2;     \ // XTMP2 = {W[0], W[-1], W[-2], W[-3]}
	VPSHUFD $0xFA, XTMP2, XTMP2;            \ // XTMP2 = {W[0], W[0], W[-1], W[-1]} {DDCC}
    VPSRLQ  $17, XTMP2, XTMP4;              \ // XTMP2 = W[-3] <<< 15 {xDxC}
    VPSHUFB shuff_DC00<>(SB), XTMP4, XTMP4; \ // XTMP4 = W[-3] <<< 15 {DC00}
    VPXOR   XTMP1, XTMP4, XTMP4;            \ // XTMP4 = W[-9]^W[-16] ^ (W[-3] <<< 15) {DCxx}
    VPSHUFD $0xFA, XTMP4, XTMP4;            \ // XTMP4 = W[-9]^W[-16] ^ (W[-3] <<< 15) {DDCC}
    VPSRLQ  $17, XTMP4,XTMP2;               \
    VPSRLQ  $9, XTMP4,XTMP3;                \
    VPXOR   XTMP2, XTMP4, XTMP4;            \
    VPXOR   XTMP3, XTMP4, XTMP4;            \ // XTMP4 = p1 {xDxC}
    VPSHUFB shuff_DC00<>(SB), XTMP4, XTMP4; \ // XTMP4 = p1 {DC00}
    VPXOR   XTMP4, XTMP5,XDWORD0 


// 前16轮计算-0
// SRND = # of {4 round}
// T is saved in (dist_T)(TBL)(SRND*1)
// W is saved in (dist_W)(SP)(SRND*2)
// W' is saved in (dist_W + 68*4*2)(SP)(SRND*1)
#define DO_ROUND16(dist_T, dist_W, a, b, c, d, e, f, g, h) \
	;                                       \ // ################################### RND 0 - 15 ###########################
	RORXL   $(32-12), a, y2;                \ // y2 = a <<< 12
    MOVL    y2, y3;                         \
	ADDL    e, y3;                          \ // y3 = (a <<< 12) + e
    ADDL    (dist_T)(TBL)(SRND*1), y3;      \ // y3 = (a <<< 12) + e + T
    RORXL   $(32-7), y3, y3;                \ // y3 = ss1
    ADDL    y3, h;                          \ // h = h+ss1
    XORL    y2, y3;                         \ // y3 = ss2
    ADDL    y3, d;                          \ // d = d+ss2
    ;                                       \
    ADDL    (dist_W)(SP)(SRND*2), h;        \ // h = h + ss1 + w
    ADDL    (dist_W+68*4*2)(SP)(SRND*2), d; \ // d = d + ss2 + w'
    ;                                       \
	MOVL    a, y1;                          \ // y1 = a     //FF //PARITY
    XORL    b, y1;                          \ // y1 = a^b   //FF //PARITY
    XORL    c, y1;                          \ // y1 = a^b^c //FF //PARITY
    ADDL    y1, d;                          \ // d = TT1
    ;                                       \
    MOVL    e, y2;                          \ // y2 = e		// GG  //PARITY
    XORL    f, y2;                          \ // y2 = e^f   // GG  //PARITY
    XORL    g, y2;                          \ // y2 = e^f^g // GG  //PARITY
    ADDL    y2, h;                          \ // h = TT2
    ;                                       \
	RORXL   $(32-8), h, y0;                 \ // y0 = TT2<<<8
    XORL    h,y0;                           \ // y0 = (TT2<<<8)^TT2
    RORXL   $(32-9), y0, y0;                \ // y0 = ((TT2<<<8)^TT2)<<<9
    XORL    y0, h;                          \ // h = p0(TT2)
    ;                                       \
    RORXL   $(32-9), b, b;                  \
    RORXL   $(32-19), f, f

// 后48轮计算
#define DO_ROUND48(dist_T, dist_W, a, b, c, d, e, f, g, h) \
	;                                       \ // ################################### RND 16 - 63 ###########################
	RORXL   $(32-12), a, y2;                \ // y2 = a <<< 12
    MOVL    y2, y3;                         \
	ADDL    e, y3;                          \ // y3 = (a <<< 12) + e
    ADDL    (dist_T)(TBL)(SRND*1), y3;      \ // y3 = (a <<< 12) + e + T
    RORXL   $(32-7), y3, y3;                \ // y3 = ss1
    ADDL    y3, h;                          \ // h = h+ss1
    XORL    y2, y3;                         \ // y3 = ss2
    ADDL    y3, d;                          \ // d = d+ss2
    ;                                       \
    ADDL    (dist_W)(SP)(SRND*2), h;        \ // h = h + ss1 + w
    ADDL    (dist_W+68*4*2)(SP)(SRND*2), d; \ // d = d + ss2 + w'
    ;                                       \
    MOVL    a, y3;                          \ // y3 = a         //FF MAJA
	ORL     c, y3;                          \ // y3 = a|c       // MAJA
	ANDL    b, y3;                          \ // y3 = (a|c)&b   // MAJA
	MOVL    a, T1;                          \ // T1 = a         // MAJB
	ANDL    c, T1;                          \ // T1 = a&c       // MAJB
	ORL     T1, y3;                         \ // y3 = MAJ = (a|c)&b)|(a&c)  // MAJ
    ADDL    y3, d;                          \ // d = TT1
    ;                                       \
    MOVL    f, y2;                          \ // y2 = f                 //GG CH
	XORL    g, y2;                          \ // y2 = f^g               // CH
	ANDL    e, y2;                          \ // y2 = (f^g)&e           // CH
	XORL    g, y2;                          \ // y2 = CH = ((f^g)&e)^g  // CH
    ADDL    y2, h;                          \ // h = TT2
    ;                                       \
	RORXL   $(32-8), h, y0;                 \ // y0 = TT2<<<8
    XORL    h,y0;                           \ // y0 = (TT2<<<8)^TT2
    RORXL   $(32-9), y0, y0;                \ // y0 = ((TT2<<<8)^TT2)<<<9
    XORL    y0, h;                          \ // h = p0(TT2)
    ;                                       \
    RORXL   $(32-9), b, b;                  \
    RORXL   $(32-19), f, f


// stack:
//         block0    block1    
//  0*8:   W[0:4]    V[0:4]    
//  1*8:   W[4:8]    V[4:8]  
//          ...
// 67*8:   W[64:68]  V[64:68]
// 68*8:   W'[0:4]   V'[0:4]
// 69*8:   W'[4:8]   V'[4:8]
//          ...
// 135*8:  W'[64:68]  V'[64:68]
// 136*8:  _INP_END(SP) - Pointer to the last block
// 137*8:  _INP(SP)     - Save INP in round computation.
// 
// STACK_SIZE = 1088+8+8 = 1104
TEXT ·blockAsmAVX2(SB), 0, $1104-32
	MOVQ dig+0(FP), CTX
	MOVQ p_base+8(FP), INP
	MOVQ p_len+16(FP), NUM_BYTES

	LEAQ -64(INP)(NUM_BYTES*1), NUM_BYTES // Pointer to the last block
	MOVQ NUM_BYTES, _INP_END(SP) // save to stack

	CMPQ NUM_BYTES, INP
	JE   avx2_only_one_block

	// Load initial digest
	MOVL 0(CTX), a  // a = H0
	MOVL 4(CTX), b  // b = H1
	MOVL 8(CTX), c  // c = H2
	MOVL 12(CTX), d // d = H3
	MOVL 16(CTX), e // e = H4
	MOVL 20(CTX), f // f = H5
	MOVL 24(CTX), g // g = H6
	MOVL 28(CTX), h // h = H7

avx2_loop0: // at each iteration works with one block (512 bit)

    // load two blocks，64*2 bytes
	VMOVDQU (0*32)(INP), XTMP0 // p[0:4]
	VMOVDQU (1*32)(INP), XTMP1
	VMOVDQU (2*32)(INP), XTMP2
	VMOVDQU (3*32)(INP), XTMP3

	VMOVDQU flip_mask<>(SB), BYTE_FLIP_MASK

	// Apply Byte Flip Mask: LE -> BE
	VPSHUFB BYTE_FLIP_MASK, XTMP0, XTMP0
	VPSHUFB BYTE_FLIP_MASK, XTMP1, XTMP1
	VPSHUFB BYTE_FLIP_MASK, XTMP2, XTMP2
	VPSHUFB BYTE_FLIP_MASK, XTMP3, XTMP3

    // XTMP0:XTMP1 - first block
    // XTMP0: w7, w6, w5, w4, w3, w2, w1,w0
    // XTMP1: w15,w14,w13,w12,w11,w10,w9,w8 
    // XTMP3:XTMP2 - second block
    // XTMP2: u7, u6, u5, u4, u3, u2, u1,u0
    // XTMP3: u15,u14,u13,u12,u11,u10,u9,u8 

    // XDWORD0: u3, u2, u1, u0, w3, w2, w1,w0
    // XDWORD1: u7, u6, u5, u4, w7, w6, w5, w4
    // XDWORD2: u11,u10,u9, u8, w11,w10,w9,w8 
    // XDWORD3: u15,u14,u13,u12,w15,w14,w13,w12

	// Transpose data into high/low parts
	VPERM2I128 $0x20, XTMP2, XTMP0, XDWORD0 // w3, w2, w1, w0
	VPERM2I128 $0x31, XTMP2, XTMP0, XDWORD1 // w7, w6, w5, w4
	VPERM2I128 $0x20, XTMP3, XTMP1, XDWORD2 // w11, w10, w9, w8
	VPERM2I128 $0x31, XTMP3, XTMP1, XDWORD3 // w15, w14, w13, w12
	MOVQ $T256<>(SB), TBL // Loading address of table with round-specific constants

avx2_last_block_enter:
	ADDQ $64, INP
	MOVQ INP, _INP(SP)
	XORQ SRND, SRND  // SRND increace 16 of each 4 rounds (dist of T)

    // for w0 - w15
	// Do 4 rounds and scheduling
	VMOVDQU XDWORD0, (_XFER + 0*32)(SP)(SRND*2)
    VPXOR   XDWORD0, XDWORD1, XFER
	VMOVDQU XFER, (_XFER + 0*32+68*4*2)(SP)(SRND*2)
    SM3_SCHED(XDWORD0, XDWORD1, XDWORD2, XDWORD3)
    DO_ROUND16(0*4, 0*32+0, a, b, c, d, e, f, g, h)
    DO_ROUND16(1*4, 0*32+4, d, a, b, c, h, e, f, g)
    DO_ROUND16(2*4, 0*32+8, c, d, a, b, g, h, e, f)
    DO_ROUND16(3*4, 0*32+12, b, c, d, a, f, g, h, e)

    VMOVDQU XDWORD1, (_XFER + 1*32)(SP)(SRND*2)
    VPXOR   XDWORD1, XDWORD2, XFER
	VMOVDQU XFER, (_XFER + 1*32+68*4*2)(SP)(SRND*2)
    SM3_SCHED(XDWORD1, XDWORD2, XDWORD3, XDWORD0)
    DO_ROUND16(4*4, 1*32+0, a, b, c, d, e, f, g, h)
    DO_ROUND16(5*4, 1*32+4, d, a, b, c, h, e, f, g)
    DO_ROUND16(6*4, 1*32+8, c, d, a, b, g, h, e, f)
    DO_ROUND16(7*4, 1*32+12, b, c, d, a, f, g, h, e)

    VMOVDQU XDWORD2, (_XFER + 2*32)(SP)(SRND*2)
    VPXOR   XDWORD2, XDWORD3, XFER
	VMOVDQU XFER, (_XFER + 2*32+68*4*2)(SP)(SRND*2)
    SM3_SCHED(XDWORD2, XDWORD3, XDWORD0, XDWORD1)
    DO_ROUND16(8*4, 2*32+0, a, b, c, d, e, f, g, h)
    DO_ROUND16(9*4, 2*32+4, d, a, b, c, h, e, f, g)
    DO_ROUND16(10*4,2*32+8, c, d, a, b, g, h, e, f)
    DO_ROUND16(11*4,2*32+12, b, c, d, a, f, g, h, e)

    VMOVDQU XDWORD3, (_XFER + 3*32)(SP)(SRND*2)
    VPXOR   XDWORD3, XDWORD0, XFER
	VMOVDQU XFER, (_XFER + 3*32+68*4*2)(SP)(SRND*2)
    SM3_SCHED(XDWORD3, XDWORD0, XDWORD1, XDWORD2)
    DO_ROUND16(12*4, 3*32+0, a, b, c, d, e, f, g, h)
    DO_ROUND16(13*4, 3*32+4, d, a, b, c, h, e, f, g)
    DO_ROUND16(14*4, 3*32+8, c, d, a, b, g, h, e, f)
    DO_ROUND16(15*4, 3*32+12, b, c, d, a, f, g, h, e)
	
    ADDQ $4*16, SRND

avx2_loop1: 
    // for w16 - w47 with scheduling (32 rounds)
    VMOVDQU XDWORD0, (_XFER + 0*32)(SP)(SRND*2)
    VPXOR   XDWORD0, XDWORD1, XFER
	VMOVDQU XFER, (_XFER + 0*32+68*4*2)(SP)(SRND*2)
    SM3_SCHED(XDWORD0, XDWORD1, XDWORD2, XDWORD3)
    DO_ROUND48(0*4, 0*32+0, a, b, c, d, e, f, g, h)
    DO_ROUND48(1*4, 0*32+4, d, a, b, c, h, e, f, g)
    DO_ROUND48(2*4, 0*32+8, c, d, a, b, g, h, e, f)
    DO_ROUND48(3*4, 0*32+12, b, c, d, a, f, g, h, e)

    VMOVDQU XDWORD1, (_XFER + 1*32)(SP)(SRND*2)
    VPXOR   XDWORD1, XDWORD2, XFER
	VMOVDQU XFER, (_XFER + 1*32+68*4*2)(SP)(SRND*2)
    SM3_SCHED(XDWORD1, XDWORD2, XDWORD3, XDWORD0)
    DO_ROUND48(4*4, 1*32+0, a, b, c, d, e, f, g, h)
    DO_ROUND48(5*4, 1*32+4, d, a, b, c, h, e, f, g)
    DO_ROUND48(6*4, 1*32+8, c, d, a, b, g, h, e, f)
    DO_ROUND48(7*4, 1*32+12, b, c, d, a, f, g, h, e)

    VMOVDQU XDWORD2, (_XFER + 2*32)(SP)(SRND*2)
    VPXOR   XDWORD2, XDWORD3, XFER
	VMOVDQU XFER, (_XFER + 2*32+68*4*2)(SP)(SRND*2)
    SM3_SCHED(XDWORD2, XDWORD3, XDWORD0, XDWORD1)
    DO_ROUND48(8*4, 2*32+0, a, b, c, d, e, f, g, h)
    DO_ROUND48(9*4, 2*32+4, d, a, b, c, h, e, f, g)
    DO_ROUND48(10*4,2*32+8, c, d, a, b, g, h, e, f)
    DO_ROUND48(11*4,2*32+12, b, c, d, a, f, g, h, e)

    VMOVDQU XDWORD3, (_XFER + 3*32)(SP)(SRND*2)
    VPXOR   XDWORD3, XDWORD0, XFER
	VMOVDQU XFER, (_XFER + 3*32+68*4*2)(SP)(SRND*2)
    SM3_SCHED(XDWORD3, XDWORD0, XDWORD1, XDWORD2)
    DO_ROUND48(12*4,3*32+0, a, b, c, d, e, f, g, h)
    DO_ROUND48(13*4,3*32+4, d, a, b, c, h, e, f, g)
    DO_ROUND48(14*4,3*32+8, c, d, a, b, g, h, e, f)
    DO_ROUND48(15*4,3*32+12, b, c, d, a, f, g, h, e)

    ADDQ $4*16, SRND
	CMPQ SRND, $12*16
	JB   avx2_loop1

	// w48 - w63 processed with one scheduling (last 16 rounds)
    VMOVDQU XDWORD0, (_XFER + 0*32)(SP)(SRND*2)
    VPXOR   XDWORD0, XDWORD1, XFER
	VMOVDQU XFER, (_XFER + 0*32+68*4*2)(SP)(SRND*2)
    SM3_SCHED(XDWORD0, XDWORD1, XDWORD2, XDWORD3) // scheduling XDWORD0 for W64-W67
    DO_ROUND48(0*4, 0*32+0, a, b, c, d, e, f, g, h)
    DO_ROUND48(1*4, 0*32+4, d, a, b, c, h, e, f, g)
    DO_ROUND48(2*4, 0*32+8, c, d, a, b, g, h, e, f)
    DO_ROUND48(3*4, 0*32+12, b, c, d, a, f, g, h, e)

    VMOVDQU XDWORD1, (_XFER + 1*32)(SP)(SRND*2)
    VPXOR   XDWORD1, XDWORD2, XFER
	VMOVDQU XFER, (_XFER + 1*32+68*4*2)(SP)(SRND*2)
    DO_ROUND48(4*4, 1*32+0, a, b, c, d, e, f, g, h)
    DO_ROUND48(5*4, 1*32+4, d, a, b, c, h, e, f, g)
    DO_ROUND48(6*4, 1*32+8, c, d, a, b, g, h, e, f)
    DO_ROUND48(7*4, 1*32+12, b, c, d, a, f, g, h, e)

    VMOVDQU XDWORD2, (_XFER + 2*32)(SP)(SRND*2)
    VPXOR   XDWORD2, XDWORD3, XFER
	VMOVDQU XFER, (_XFER + 2*32+68*4*2)(SP)(SRND*2)
    DO_ROUND48(8*4, 2*32+0, a, b, c, d, e, f, g, h)
    DO_ROUND48(9*4, 2*32+4, d, a, b, c, h, e, f, g)
    DO_ROUND48(10*4,2*32+8, c, d, a, b, g, h, e, f)
    DO_ROUND48(11*4,2*32+12, b, c, d, a, f, g, h, e)

    VMOVDQU XDWORD3, (_XFER + 3*32)(SP)(SRND*2)
    VPXOR   XDWORD3, XDWORD0, XFER
	VMOVDQU XFER, (_XFER + 3*32+68*4*2)(SP)(SRND*2)
    DO_ROUND48(12*4, 3*32+0, a, b, c, d, e, f, g, h)
    DO_ROUND48(13*4, 3*32+4, d, a, b, c, h, e, f, g)
    DO_ROUND48(14*4, 3*32+8, c, d, a, b, g, h, e, f)
    DO_ROUND48(15*4, 3*32+12, b, c, d, a, f, g, h, e)

	MOVQ dig+0(FP), CTX // d.h[8]
	MOVQ _INP(SP), INP

	xorm(  0(CTX), a)
	xorm(  4(CTX), b)
	xorm(  8(CTX), c)
	xorm( 12(CTX), d)
	xorm( 16(CTX), e)
	xorm( 20(CTX), f)
	xorm( 24(CTX), g)
	xorm( 28(CTX), h)

	CMPQ _INP_END(SP), INP
	JB   done_hash

	XORQ SRND, SRND

avx2_loop3: // Do second block using previously scheduled results
	DO_ROUND16(0, 16+0, a, b, c, d, e, f, g, h)
    DO_ROUND16(4, 16+4, d, a, b, c, h, e, f, g)
    DO_ROUND16(8, 16+8, c, d, a, b, g, h, e, f)
    DO_ROUND16(12, 16+12, b, c, d, a, f, g, h, e)

	ADDQ $16, SRND
	CMPQ SRND, $4*16
	JB   avx2_loop3
avx2_loop4:  
	DO_ROUND48(0, 16+0,a, b, c, d, e, f, g, h)
    DO_ROUND48(4, 16+4,d, a, b, c, h, e, f, g)
    DO_ROUND48(8, 16+8,c, d, a, b, g, h, e, f)
    DO_ROUND48(12, 16+12, b, c, d, a, f, g, h, e)

	ADDQ $16, SRND
	CMPQ SRND, $16*16
	JB   avx2_loop4

	MOVQ dig+0(FP), CTX // d.h[8]
	MOVQ _INP(SP), INP
	ADDQ $64, INP

	xorm(  0(CTX), a)
	xorm(  4(CTX), b)
	xorm(  8(CTX), c)
	xorm( 12(CTX), d)
	xorm( 16(CTX), e)
	xorm( 20(CTX), f)
	xorm( 24(CTX), g)
	xorm( 28(CTX), h)

	CMPQ _INP_END(SP), INP
	JA   avx2_loop0
	JB   done_hash

avx2_do_last_block:

	VMOVDQU 0(INP), XWORD0
	VMOVDQU 16(INP), XWORD1
	VMOVDQU 32(INP), XWORD2
	VMOVDQU 48(INP), XWORD3

	VMOVDQU flip_mask<>(SB), BYTE_FLIP_MASK

	VPSHUFB X_BYTE_FLIP_MASK, XWORD0, XWORD0
	VPSHUFB X_BYTE_FLIP_MASK, XWORD1, XWORD1
	VPSHUFB X_BYTE_FLIP_MASK, XWORD2, XWORD2
	VPSHUFB X_BYTE_FLIP_MASK, XWORD3, XWORD3
	MOVQ $T256<>(SB), TBL

	JMP avx2_last_block_enter

avx2_only_one_block:
	// Load initial digest
	MOVL 0(CTX), a  // a = H0
	MOVL 4(CTX), b  // b = H1
	MOVL 8(CTX), c  // c = H2
	MOVL 12(CTX), d // d = H3
	MOVL 16(CTX), e // e = H4
	MOVL 20(CTX), f // f = H5
	MOVL 24(CTX), g // g = H6
	MOVL 28(CTX), h // h = H7

	JMP avx2_do_last_block

done_hash:
	VZEROUPPER
	RET

// shuffle byte order from LE to BE
DATA flip_mask<>+0x00(SB)/8, $0x0405060700010203
DATA flip_mask<>+0x08(SB)/8, $0x0c0d0e0f08090a0b
DATA flip_mask<>+0x10(SB)/8, $0x0405060700010203
DATA flip_mask<>+0x18(SB)/8, $0x0c0d0e0f08090a0b
GLOBL flip_mask<>(SB), 8, $32

// shuffle xBxA -> 00BA
DATA shuff_00BA<>+0x00(SB)/8, $0x0b0a090803020100
DATA shuff_00BA<>+0x08(SB)/8, $0xFFFFFFFFFFFFFFFF
DATA shuff_00BA<>+0x10(SB)/8, $0x0b0a090803020100
DATA shuff_00BA<>+0x18(SB)/8, $0xFFFFFFFFFFFFFFFF
GLOBL shuff_00BA<>(SB), 8, $32

// shuffle xDxC -> DC00
DATA shuff_DC00<>+0x00(SB)/8, $0xFFFFFFFFFFFFFFFF
DATA shuff_DC00<>+0x08(SB)/8, $0x0b0a090803020100
DATA shuff_DC00<>+0x10(SB)/8, $0xFFFFFFFFFFFFFFFF
DATA shuff_DC00<>+0x18(SB)/8, $0x0b0a090803020100
GLOBL shuff_DC00<>(SB), 8, $32

// rotate of Tj: rotT[i] = Tj << (j mod 32)
DATA T256<>+0x0(SB)/4, $0x79cc4519
DATA T256<>+0x4(SB)/4, $0xf3988a32
DATA T256<>+0x8(SB)/4, $0xe7311465
DATA T256<>+0xc(SB)/4, $0xce6228cb
DATA T256<>+0x10(SB)/4, $0x9cc45197
DATA T256<>+0x14(SB)/4, $0x3988a32f
DATA T256<>+0x18(SB)/4, $0x7311465e
DATA T256<>+0x1c(SB)/4, $0xe6228cbc
DATA T256<>+0x20(SB)/4, $0xcc451979
DATA T256<>+0x24(SB)/4, $0x988a32f3
DATA T256<>+0x28(SB)/4, $0x311465e7
DATA T256<>+0x2c(SB)/4, $0x6228cbce
DATA T256<>+0x30(SB)/4, $0xc451979c
DATA T256<>+0x34(SB)/4, $0x88a32f39
DATA T256<>+0x38(SB)/4, $0x11465e73
DATA T256<>+0x3c(SB)/4, $0x228cbce6
DATA T256<>+0x40(SB)/4, $0x9d8a7a87
DATA T256<>+0x44(SB)/4, $0x3b14f50f
DATA T256<>+0x48(SB)/4, $0x7629ea1e
DATA T256<>+0x4c(SB)/4, $0xec53d43c
DATA T256<>+0x50(SB)/4, $0xd8a7a879
DATA T256<>+0x54(SB)/4, $0xb14f50f3
DATA T256<>+0x58(SB)/4, $0x629ea1e7
DATA T256<>+0x5c(SB)/4, $0xc53d43ce
DATA T256<>+0x60(SB)/4, $0x8a7a879d
DATA T256<>+0x64(SB)/4, $0x14f50f3b
DATA T256<>+0x68(SB)/4, $0x29ea1e76
DATA T256<>+0x6c(SB)/4, $0x53d43cec
DATA T256<>+0x70(SB)/4, $0xa7a879d8
DATA T256<>+0x74(SB)/4, $0x4f50f3b1
DATA T256<>+0x78(SB)/4, $0x9ea1e762
DATA T256<>+0x7c(SB)/4, $0x3d43cec5
DATA T256<>+0x80(SB)/4, $0x7a879d8a
DATA T256<>+0x84(SB)/4, $0xf50f3b14
DATA T256<>+0x88(SB)/4, $0xea1e7629
DATA T256<>+0x8c(SB)/4, $0xd43cec53
DATA T256<>+0x90(SB)/4, $0xa879d8a7
DATA T256<>+0x94(SB)/4, $0x50f3b14f
DATA T256<>+0x98(SB)/4, $0xa1e7629e
DATA T256<>+0x9c(SB)/4, $0x43cec53d
DATA T256<>+0xa0(SB)/4, $0x879d8a7a
DATA T256<>+0xa4(SB)/4, $0x0f3b14f5
DATA T256<>+0xa8(SB)/4, $0x1e7629ea
DATA T256<>+0xac(SB)/4, $0x3cec53d4
DATA T256<>+0xb0(SB)/4, $0x79d8a7a8
DATA T256<>+0xb4(SB)/4, $0xf3b14f50
DATA T256<>+0xb8(SB)/4, $0xe7629ea1
DATA T256<>+0xbc(SB)/4, $0xcec53d43
DATA T256<>+0xc0(SB)/4, $0x9d8a7a87
DATA T256<>+0xc4(SB)/4, $0x3b14f50f
DATA T256<>+0xc8(SB)/4, $0x7629ea1e
DATA T256<>+0xcc(SB)/4, $0xec53d43c
DATA T256<>+0xd0(SB)/4, $0xd8a7a879
DATA T256<>+0xd4(SB)/4, $0xb14f50f3
DATA T256<>+0xd8(SB)/4, $0x629ea1e7
DATA T256<>+0xdc(SB)/4, $0xc53d43ce
DATA T256<>+0xe0(SB)/4, $0x8a7a879d
DATA T256<>+0xe4(SB)/4, $0x14f50f3b
DATA T256<>+0xe8(SB)/4, $0x29ea1e76
DATA T256<>+0xec(SB)/4, $0x53d43cec
DATA T256<>+0xf0(SB)/4, $0xa7a879d8
DATA T256<>+0xf4(SB)/4, $0x4f50f3b1
DATA T256<>+0xf8(SB)/4, $0x9ea1e762
DATA T256<>+0xfc(SB)/4, $0x3d43cec5
GLOBL T256<>(SB), (NOPTR + RODATA), $256
