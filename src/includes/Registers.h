/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef  TRITON_REGISTERS_H
#define  TRITON_REGISTERS_H

#include "CpuSize.h"


enum regID_t
{

  /* Register ID used in the Taint and Symbolic Engines */
  /* 0  */ ID_INVALID = 0,

  #if defined(__x86_64__) || defined(_M_X64)
  /*Only for 64bits architectures*/
  /* 1  */ ID_RAX,
  /* 2  */ ID_RBX,
  /* 3  */ ID_RCX,
  /* 4  */ ID_RDX,
  /* 5  */ ID_RDI,
  /* 6  */ ID_RSI,
  /* 7  */ ID_RBP,
  /* 8  */ ID_RSP,
  /* 9  */ ID_RIP,
  /* 10 */ ID_R8,
  /* 11 */ ID_R9,
  /* 12 */ ID_R10,
  /* 13 */ ID_R11,
  /* 14 */ ID_R12,
  /* 15 */ ID_R13,
  /* 16 */ ID_R14,
  /* 17 */ ID_R15,
  #endif

  /* SSE */
  /* 18 */ ID_XMM0,
  /* 19 */ ID_XMM1,
  /* 20 */ ID_XMM2,
  /* 21 */ ID_XMM3,
  /* 22 */ ID_XMM4,
  /* 23 */ ID_XMM5,
  /* 24 */ ID_XMM6,
  /* 25 */ ID_XMM7,

  #if defined(__x86_64__) || defined(_M_X64)
  /* 26 */ ID_XMM8,
  /* 27 */ ID_XMM9,
  /* 28 */ ID_XMM10,
  /* 29 */ ID_XMM11,
  /* 30 */ ID_XMM12,
  /* 31 */ ID_XMM13,
  /* 32 */ ID_XMM14,
  /* 33 */ ID_XMM15,
  #endif

  #if defined(__i386) || defined(_M_IX86)
  /* 1  */ ID_EAX,
  /* 2  */ ID_EBX,
  /* 3  */ ID_ECX,
  /* 4  */ ID_EDX,
  /* 5  */ ID_EDI,
  /* 6  */ ID_ESI,
  /* 7  */ ID_EBP,
  /* 8  */ ID_ESP,
  /* 9  */ ID_EIP,
  #endif

  #if defined(__x86_64__) || defined(_M_X64)
  /* 34 */ ID_RFLAGS,
  #endif
  #if defined(__i386) || defined(_M_IX86)
  /* 34 */ ID_EFLAGS,
  #endif
  /* Flags ID used in the Taint and Symbolic Engines */
  /* 35 */ ID_AF,
  /* 36 */ ID_CF,
  /* 37 */ ID_DF,
  /* 38 */ ID_IF,
  /* 39 */ ID_OF,
  /* 40 */ ID_PF,
  /* 41 */ ID_SF,
  /* 42 */ ID_TF,
  /* 43 */ ID_ZF,

  /* Must be the last item */
  ID_LAST_ITEM
};

#define isFlagId(x)   ((x >= ID_AF && x <= ID_ZF) ? true : false)

#if defined(__x86_64__) || defined(_M_X64)
#define isRegId(x)    ((x >= ID_RAX && x <= ID_RFLAGS) ? true : false)
#define isSSERegId(x) ((x >= ID_XMM0 && x <= ID_XMM15) ? true : false)
#define ID_FLAGS ID_RFLAGS
#define ID_IP	 ID_RIP
#define ID_SP	 ID_RSP
#define ID_BP	 ID_RBP
#endif

#if defined(__i386) || defined(_M_IX86)
#define isRegId(x)    ((x >= ID_EAX && x <= ID_EFLAGS) ? true : false)
#define isSSERegId(x) ((x >= ID_XMM0 && x <= ID_XMM7) ? true : false)
#define ID_FLAGS ID_EFLAGS
#define ID_IP	 ID_EIP
#define ID_SP	 ID_ESP
#define ID_BP	 ID_EBP
#endif

#include "TmpReg.h"

#endif //__REGISTERS_H__

