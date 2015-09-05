/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef   TMPREG_H
#define   TMPREG_H

#include "PINConverter.h"
#include "RegisterOperand.h"
#include "Registers.h"

extern RegisterOperand tmp_reg_rax;
extern RegisterOperand tmp_reg_rbx;
extern RegisterOperand tmp_reg_rcx;
extern RegisterOperand tmp_reg_rdx;
extern RegisterOperand tmp_reg_rdi;
extern RegisterOperand tmp_reg_rsi;
extern RegisterOperand tmp_reg_rsp;
extern RegisterOperand tmp_reg_rbp;
extern RegisterOperand tmp_reg_rip;
extern RegisterOperand tmp_reg_r8;
extern RegisterOperand tmp_reg_r9;
extern RegisterOperand tmp_reg_r10;
extern RegisterOperand tmp_reg_r11;
extern RegisterOperand tmp_reg_r12;
extern RegisterOperand tmp_reg_r13;
extern RegisterOperand tmp_reg_r14;
extern RegisterOperand tmp_reg_r15;
extern RegisterOperand tmp_reg_xmm0;
extern RegisterOperand tmp_reg_xmm1;
extern RegisterOperand tmp_reg_xmm2;
extern RegisterOperand tmp_reg_xmm3;
extern RegisterOperand tmp_reg_xmm4;
extern RegisterOperand tmp_reg_xmm5;
extern RegisterOperand tmp_reg_xmm6;
extern RegisterOperand tmp_reg_xmm7;
extern RegisterOperand tmp_reg_xmm8;
extern RegisterOperand tmp_reg_xmm9;
extern RegisterOperand tmp_reg_xmm10;
extern RegisterOperand tmp_reg_xmm11;
extern RegisterOperand tmp_reg_xmm12;
extern RegisterOperand tmp_reg_xmm13;
extern RegisterOperand tmp_reg_xmm14;
extern RegisterOperand tmp_reg_xmm15;
extern RegisterOperand tmp_reg_rflags;
extern RegisterOperand tmp_flag_af;
extern RegisterOperand tmp_flag_cf;
extern RegisterOperand tmp_flag_df;
extern RegisterOperand tmp_flag_if;
extern RegisterOperand tmp_flag_of;
extern RegisterOperand tmp_flag_pf;
extern RegisterOperand tmp_flag_sf;
extern RegisterOperand tmp_flag_tf;
extern RegisterOperand tmp_flag_zf;

RegisterOperand createTmpReg(uint64 tritonRegId);
RegisterOperand createTmpFlag(uint64 tritonFlagId);

#define ID_TMP_RAX    tmp_reg_rax
#define ID_TMP_RBX    tmp_reg_rbx
#define ID_TMP_RCX    tmp_reg_rcx
#define ID_TMP_RDX    tmp_reg_rdx
#define ID_TMP_RDI    tmp_reg_rdi
#define ID_TMP_RSI    tmp_reg_rsi
#define ID_TMP_RSP    tmp_reg_rsp
#define ID_TMP_RBP    tmp_reg_rbp
#define ID_TMP_RIP    tmp_reg_rip
#define ID_TMP_R8     tmp_reg_r8
#define ID_TMP_R9     tmp_reg_r9
#define ID_TMP_R10    tmp_reg_r10
#define ID_TMP_R11    tmp_reg_r11
#define ID_TMP_R12    tmp_reg_r12
#define ID_TMP_R13    tmp_reg_r13
#define ID_TMP_R14    tmp_reg_r14
#define ID_TMP_R15    tmp_reg_r15
#define ID_TMP_XMM0   tmp_reg_xmm0
#define ID_TMP_XMM1   tmp_reg_xmm1
#define ID_TMP_XMM2   tmp_reg_xmm2
#define ID_TMP_XMM3   tmp_reg_xmm3
#define ID_TMP_XMM4   tmp_reg_xmm4
#define ID_TMP_XMM5   tmp_reg_xmm5
#define ID_TMP_XMM6   tmp_reg_xmm6
#define ID_TMP_XMM7   tmp_reg_xmm7
#define ID_TMP_XMM8   tmp_reg_xmm8
#define ID_TMP_XMM9   tmp_reg_xmm9
#define ID_TMP_XMM10  tmp_reg_xmm10
#define ID_TMP_XMM11  tmp_reg_xmm11
#define ID_TMP_XMM12  tmp_reg_xmm12
#define ID_TMP_XMM13  tmp_reg_xmm13
#define ID_TMP_XMM14  tmp_reg_xmm14
#define ID_TMP_XMM15  tmp_reg_xmm15
#define ID_TMP_RFLAGS tmp_reg_rflags
#define ID_TMP_AF     tmp_flag_af
#define ID_TMP_CF     tmp_flag_cf
#define ID_TMP_DF     tmp_flag_df
#define ID_TMP_IF     tmp_flag_if
#define ID_TMP_OF     tmp_flag_of
#define ID_TMP_PF     tmp_flag_pf
#define ID_TMP_SF     tmp_flag_sf
#define ID_TMP_TF     tmp_flag_tf
#define ID_TMP_ZF     tmp_flag_zf

#endif     /* !TMPREG_H */

