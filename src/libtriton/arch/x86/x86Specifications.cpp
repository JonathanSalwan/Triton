//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/architecture.hpp>
#include <triton/cpuSize.hpp>
#include <triton/externalLibs.hpp>
#include <triton/x86Specifications.hpp>



namespace triton {
  namespace arch {
    namespace x86 {

      /*
       * Inside semantics, sometime we have to use references to registers.
       * TRITON_X86_REG_RAX, TRITON_X86_REG_RBX, ..., TRITON_X86_REG_AF...
       * are now available for a temporary access to the triton::arch::Register
       * class. By default, these X86_REG are empty. We must use init32 or init64 before.
       */

      triton::arch::Register x86_reg_invalid = triton::arch::Register();

      triton::arch::Register x86_reg_rax     = triton::arch::Register();
      triton::arch::Register x86_reg_eax     = triton::arch::Register();
      triton::arch::Register x86_reg_ax      = triton::arch::Register();
      triton::arch::Register x86_reg_ah      = triton::arch::Register();
      triton::arch::Register x86_reg_al      = triton::arch::Register();

      triton::arch::Register x86_reg_rbx     = triton::arch::Register();
      triton::arch::Register x86_reg_ebx     = triton::arch::Register();
      triton::arch::Register x86_reg_bx      = triton::arch::Register();
      triton::arch::Register x86_reg_bh      = triton::arch::Register();
      triton::arch::Register x86_reg_bl      = triton::arch::Register();

      triton::arch::Register x86_reg_rcx     = triton::arch::Register();
      triton::arch::Register x86_reg_ecx     = triton::arch::Register();
      triton::arch::Register x86_reg_cx      = triton::arch::Register();
      triton::arch::Register x86_reg_ch      = triton::arch::Register();
      triton::arch::Register x86_reg_cl      = triton::arch::Register();

      triton::arch::Register x86_reg_rdx     = triton::arch::Register();
      triton::arch::Register x86_reg_edx     = triton::arch::Register();
      triton::arch::Register x86_reg_dx      = triton::arch::Register();
      triton::arch::Register x86_reg_dh      = triton::arch::Register();
      triton::arch::Register x86_reg_dl      = triton::arch::Register();

      triton::arch::Register x86_reg_rdi     = triton::arch::Register();
      triton::arch::Register x86_reg_edi     = triton::arch::Register();
      triton::arch::Register x86_reg_di      = triton::arch::Register();
      triton::arch::Register x86_reg_dil     = triton::arch::Register();

      triton::arch::Register x86_reg_rsi     = triton::arch::Register();
      triton::arch::Register x86_reg_esi     = triton::arch::Register();
      triton::arch::Register x86_reg_si      = triton::arch::Register();
      triton::arch::Register x86_reg_sil     = triton::arch::Register();

      triton::arch::Register x86_reg_rsp     = triton::arch::Register();
      triton::arch::Register x86_reg_esp     = triton::arch::Register();
      triton::arch::Register x86_reg_sp      = triton::arch::Register();
      triton::arch::Register x86_reg_spl     = triton::arch::Register();
      triton::arch::Register x86_reg_stack   = triton::arch::Register();

      triton::arch::Register x86_reg_rbp     = triton::arch::Register();
      triton::arch::Register x86_reg_ebp     = triton::arch::Register();
      triton::arch::Register x86_reg_bp      = triton::arch::Register();
      triton::arch::Register x86_reg_bpl     = triton::arch::Register();

      triton::arch::Register x86_reg_rip     = triton::arch::Register();
      triton::arch::Register x86_reg_eip     = triton::arch::Register();
      triton::arch::Register x86_reg_ip      = triton::arch::Register();
      triton::arch::Register x86_reg_pc      = triton::arch::Register();

      triton::arch::Register x86_reg_eflags  = triton::arch::Register();

      triton::arch::Register x86_reg_r8      = triton::arch::Register();
      triton::arch::Register x86_reg_r8d     = triton::arch::Register();
      triton::arch::Register x86_reg_r8w     = triton::arch::Register();
      triton::arch::Register x86_reg_r8b     = triton::arch::Register();

      triton::arch::Register x86_reg_r9      = triton::arch::Register();
      triton::arch::Register x86_reg_r9d     = triton::arch::Register();
      triton::arch::Register x86_reg_r9w     = triton::arch::Register();
      triton::arch::Register x86_reg_r9b     = triton::arch::Register();

      triton::arch::Register x86_reg_r10     = triton::arch::Register();
      triton::arch::Register x86_reg_r10d    = triton::arch::Register();
      triton::arch::Register x86_reg_r10w    = triton::arch::Register();
      triton::arch::Register x86_reg_r10b    = triton::arch::Register();

      triton::arch::Register x86_reg_r11     = triton::arch::Register();
      triton::arch::Register x86_reg_r11d    = triton::arch::Register();
      triton::arch::Register x86_reg_r11w    = triton::arch::Register();
      triton::arch::Register x86_reg_r11b    = triton::arch::Register();

      triton::arch::Register x86_reg_r12     = triton::arch::Register();
      triton::arch::Register x86_reg_r12d    = triton::arch::Register();
      triton::arch::Register x86_reg_r12w    = triton::arch::Register();
      triton::arch::Register x86_reg_r12b    = triton::arch::Register();

      triton::arch::Register x86_reg_r13     = triton::arch::Register();
      triton::arch::Register x86_reg_r13d    = triton::arch::Register();
      triton::arch::Register x86_reg_r13w    = triton::arch::Register();
      triton::arch::Register x86_reg_r13b    = triton::arch::Register();

      triton::arch::Register x86_reg_r14     = triton::arch::Register();
      triton::arch::Register x86_reg_r14d    = triton::arch::Register();
      triton::arch::Register x86_reg_r14w    = triton::arch::Register();
      triton::arch::Register x86_reg_r14b    = triton::arch::Register();

      triton::arch::Register x86_reg_r15     = triton::arch::Register();
      triton::arch::Register x86_reg_r15d    = triton::arch::Register();
      triton::arch::Register x86_reg_r15w    = triton::arch::Register();
      triton::arch::Register x86_reg_r15b    = triton::arch::Register();

      triton::arch::Register x86_reg_mm0     = triton::arch::Register();
      triton::arch::Register x86_reg_mm1     = triton::arch::Register();
      triton::arch::Register x86_reg_mm2     = triton::arch::Register();
      triton::arch::Register x86_reg_mm3     = triton::arch::Register();
      triton::arch::Register x86_reg_mm4     = triton::arch::Register();
      triton::arch::Register x86_reg_mm5     = triton::arch::Register();
      triton::arch::Register x86_reg_mm6     = triton::arch::Register();
      triton::arch::Register x86_reg_mm7     = triton::arch::Register();

      triton::arch::Register x86_reg_xmm0    = triton::arch::Register();
      triton::arch::Register x86_reg_xmm1    = triton::arch::Register();
      triton::arch::Register x86_reg_xmm2    = triton::arch::Register();
      triton::arch::Register x86_reg_xmm3    = triton::arch::Register();
      triton::arch::Register x86_reg_xmm4    = triton::arch::Register();
      triton::arch::Register x86_reg_xmm5    = triton::arch::Register();
      triton::arch::Register x86_reg_xmm6    = triton::arch::Register();
      triton::arch::Register x86_reg_xmm7    = triton::arch::Register();
      triton::arch::Register x86_reg_xmm8    = triton::arch::Register();
      triton::arch::Register x86_reg_xmm9    = triton::arch::Register();
      triton::arch::Register x86_reg_xmm10   = triton::arch::Register();
      triton::arch::Register x86_reg_xmm11   = triton::arch::Register();
      triton::arch::Register x86_reg_xmm12   = triton::arch::Register();
      triton::arch::Register x86_reg_xmm13   = triton::arch::Register();
      triton::arch::Register x86_reg_xmm14   = triton::arch::Register();
      triton::arch::Register x86_reg_xmm15   = triton::arch::Register();

      triton::arch::Register x86_reg_ymm0    = triton::arch::Register();
      triton::arch::Register x86_reg_ymm1    = triton::arch::Register();
      triton::arch::Register x86_reg_ymm2    = triton::arch::Register();
      triton::arch::Register x86_reg_ymm3    = triton::arch::Register();
      triton::arch::Register x86_reg_ymm4    = triton::arch::Register();
      triton::arch::Register x86_reg_ymm5    = triton::arch::Register();
      triton::arch::Register x86_reg_ymm6    = triton::arch::Register();
      triton::arch::Register x86_reg_ymm7    = triton::arch::Register();
      triton::arch::Register x86_reg_ymm8    = triton::arch::Register();
      triton::arch::Register x86_reg_ymm9    = triton::arch::Register();
      triton::arch::Register x86_reg_ymm10   = triton::arch::Register();
      triton::arch::Register x86_reg_ymm11   = triton::arch::Register();
      triton::arch::Register x86_reg_ymm12   = triton::arch::Register();
      triton::arch::Register x86_reg_ymm13   = triton::arch::Register();
      triton::arch::Register x86_reg_ymm14   = triton::arch::Register();
      triton::arch::Register x86_reg_ymm15   = triton::arch::Register();

      triton::arch::Register x86_reg_zmm0    = triton::arch::Register();
      triton::arch::Register x86_reg_zmm1    = triton::arch::Register();
      triton::arch::Register x86_reg_zmm2    = triton::arch::Register();
      triton::arch::Register x86_reg_zmm3    = triton::arch::Register();
      triton::arch::Register x86_reg_zmm4    = triton::arch::Register();
      triton::arch::Register x86_reg_zmm5    = triton::arch::Register();
      triton::arch::Register x86_reg_zmm6    = triton::arch::Register();
      triton::arch::Register x86_reg_zmm7    = triton::arch::Register();
      triton::arch::Register x86_reg_zmm8    = triton::arch::Register();
      triton::arch::Register x86_reg_zmm9    = triton::arch::Register();
      triton::arch::Register x86_reg_zmm10   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm11   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm12   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm13   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm14   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm15   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm16   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm17   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm18   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm19   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm20   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm21   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm22   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm23   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm24   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm25   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm26   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm27   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm28   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm29   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm30   = triton::arch::Register();
      triton::arch::Register x86_reg_zmm31   = triton::arch::Register();

      triton::arch::Register x86_reg_mxcsr   = triton::arch::Register();

      triton::arch::Register x86_reg_cr0    = triton::arch::Register();
      triton::arch::Register x86_reg_cr1    = triton::arch::Register();
      triton::arch::Register x86_reg_cr2    = triton::arch::Register();
      triton::arch::Register x86_reg_cr3    = triton::arch::Register();
      triton::arch::Register x86_reg_cr4    = triton::arch::Register();
      triton::arch::Register x86_reg_cr5    = triton::arch::Register();
      triton::arch::Register x86_reg_cr6    = triton::arch::Register();
      triton::arch::Register x86_reg_cr7    = triton::arch::Register();
      triton::arch::Register x86_reg_cr8    = triton::arch::Register();
      triton::arch::Register x86_reg_cr9    = triton::arch::Register();
      triton::arch::Register x86_reg_cr10   = triton::arch::Register();
      triton::arch::Register x86_reg_cr11   = triton::arch::Register();
      triton::arch::Register x86_reg_cr12   = triton::arch::Register();
      triton::arch::Register x86_reg_cr13   = triton::arch::Register();
      triton::arch::Register x86_reg_cr14   = triton::arch::Register();
      triton::arch::Register x86_reg_cr15   = triton::arch::Register();

      triton::arch::Register x86_reg_ie      = triton::arch::Register();
      triton::arch::Register x86_reg_de      = triton::arch::Register();
      triton::arch::Register x86_reg_ze      = triton::arch::Register();
      triton::arch::Register x86_reg_oe      = triton::arch::Register();
      triton::arch::Register x86_reg_ue      = triton::arch::Register();
      triton::arch::Register x86_reg_pe      = triton::arch::Register();
      triton::arch::Register x86_reg_daz     = triton::arch::Register();
      triton::arch::Register x86_reg_im      = triton::arch::Register();
      triton::arch::Register x86_reg_dm      = triton::arch::Register();
      triton::arch::Register x86_reg_zm      = triton::arch::Register();
      triton::arch::Register x86_reg_om      = triton::arch::Register();
      triton::arch::Register x86_reg_um      = triton::arch::Register();
      triton::arch::Register x86_reg_pm      = triton::arch::Register();
      triton::arch::Register x86_reg_rl      = triton::arch::Register();
      triton::arch::Register x86_reg_rh      = triton::arch::Register();
      triton::arch::Register x86_reg_fz      = triton::arch::Register();

      triton::arch::Register x86_reg_af      = triton::arch::Register();
      triton::arch::Register x86_reg_cf      = triton::arch::Register();
      triton::arch::Register x86_reg_df      = triton::arch::Register();
      triton::arch::Register x86_reg_if      = triton::arch::Register();
      triton::arch::Register x86_reg_of      = triton::arch::Register();
      triton::arch::Register x86_reg_pf      = triton::arch::Register();
      triton::arch::Register x86_reg_sf      = triton::arch::Register();
      triton::arch::Register x86_reg_tf      = triton::arch::Register();
      triton::arch::Register x86_reg_zf      = triton::arch::Register();

      triton::arch::Register x86_reg_cs      = triton::arch::Register();
      triton::arch::Register x86_reg_ds      = triton::arch::Register();
      triton::arch::Register x86_reg_es      = triton::arch::Register();
      triton::arch::Register x86_reg_fs      = triton::arch::Register();
      triton::arch::Register x86_reg_gs      = triton::arch::Register();
      triton::arch::Register x86_reg_ss      = triton::arch::Register();


      triton::arch::Register* x86_regs[triton::arch::x86::ID_REG_LAST_ITEM] = {
        &TRITON_X86_REG_INVALID,
        &TRITON_X86_REG_RAX,
        &TRITON_X86_REG_RBX,
        &TRITON_X86_REG_RCX,
        &TRITON_X86_REG_RDX,
        &TRITON_X86_REG_RDI,
        &TRITON_X86_REG_RSI,
        &TRITON_X86_REG_RBP,
        &TRITON_X86_REG_RSP,
        &TRITON_X86_REG_RIP,
        &TRITON_X86_REG_EFLAGS,
        &TRITON_X86_REG_R8,
        &TRITON_X86_REG_R8D,
        &TRITON_X86_REG_R8W,
        &TRITON_X86_REG_R8B,
        &TRITON_X86_REG_R9,
        &TRITON_X86_REG_R9D,
        &TRITON_X86_REG_R9W,
        &TRITON_X86_REG_R9B,
        &TRITON_X86_REG_R10,
        &TRITON_X86_REG_R10D,
        &TRITON_X86_REG_R10W,
        &TRITON_X86_REG_R10B,
        &TRITON_X86_REG_R11,
        &TRITON_X86_REG_R11D,
        &TRITON_X86_REG_R11W,
        &TRITON_X86_REG_R11B,
        &TRITON_X86_REG_R12,
        &TRITON_X86_REG_R12D,
        &TRITON_X86_REG_R12W,
        &TRITON_X86_REG_R12B,
        &TRITON_X86_REG_R13,
        &TRITON_X86_REG_R13D,
        &TRITON_X86_REG_R13W,
        &TRITON_X86_REG_R13B,
        &TRITON_X86_REG_R14,
        &TRITON_X86_REG_R14D,
        &TRITON_X86_REG_R14W,
        &TRITON_X86_REG_R14B,
        &TRITON_X86_REG_R15,
        &TRITON_X86_REG_R15D,
        &TRITON_X86_REG_R15W,
        &TRITON_X86_REG_R15B,
        &TRITON_X86_REG_EAX,
        &TRITON_X86_REG_AX,
        &TRITON_X86_REG_AH,
        &TRITON_X86_REG_AL,
        &TRITON_X86_REG_EBX,
        &TRITON_X86_REG_BX,
        &TRITON_X86_REG_BH,
        &TRITON_X86_REG_BL,
        &TRITON_X86_REG_ECX,
        &TRITON_X86_REG_CX,
        &TRITON_X86_REG_CH,
        &TRITON_X86_REG_CL,
        &TRITON_X86_REG_EDX,
        &TRITON_X86_REG_DX,
        &TRITON_X86_REG_DH,
        &TRITON_X86_REG_DL,
        &TRITON_X86_REG_EDI,
        &TRITON_X86_REG_DI,
        &TRITON_X86_REG_DIL,
        &TRITON_X86_REG_ESI,
        &TRITON_X86_REG_SI,
        &TRITON_X86_REG_SIL,
        &TRITON_X86_REG_EBP,
        &TRITON_X86_REG_BP,
        &TRITON_X86_REG_BPL,
        &TRITON_X86_REG_ESP,
        &TRITON_X86_REG_SP,
        &TRITON_X86_REG_SPL,
        &TRITON_X86_REG_EIP,
        &TRITON_X86_REG_IP,
        &TRITON_X86_REG_MM0,
        &TRITON_X86_REG_MM1,
        &TRITON_X86_REG_MM2,
        &TRITON_X86_REG_MM3,
        &TRITON_X86_REG_MM4,
        &TRITON_X86_REG_MM5,
        &TRITON_X86_REG_MM6,
        &TRITON_X86_REG_MM7,
        &TRITON_X86_REG_XMM0,
        &TRITON_X86_REG_XMM1,
        &TRITON_X86_REG_XMM2,
        &TRITON_X86_REG_XMM3,
        &TRITON_X86_REG_XMM4,
        &TRITON_X86_REG_XMM5,
        &TRITON_X86_REG_XMM6,
        &TRITON_X86_REG_XMM7,
        &TRITON_X86_REG_XMM8,
        &TRITON_X86_REG_XMM9,
        &TRITON_X86_REG_XMM10,
        &TRITON_X86_REG_XMM11,
        &TRITON_X86_REG_XMM12,
        &TRITON_X86_REG_XMM13,
        &TRITON_X86_REG_XMM14,
        &TRITON_X86_REG_XMM15,
        &TRITON_X86_REG_YMM0,
        &TRITON_X86_REG_YMM1,
        &TRITON_X86_REG_YMM2,
        &TRITON_X86_REG_YMM3,
        &TRITON_X86_REG_YMM4,
        &TRITON_X86_REG_YMM5,
        &TRITON_X86_REG_YMM6,
        &TRITON_X86_REG_YMM7,
        &TRITON_X86_REG_YMM8,
        &TRITON_X86_REG_YMM9,
        &TRITON_X86_REG_YMM10,
        &TRITON_X86_REG_YMM11,
        &TRITON_X86_REG_YMM12,
        &TRITON_X86_REG_YMM13,
        &TRITON_X86_REG_YMM14,
        &TRITON_X86_REG_YMM15,
        &TRITON_X86_REG_ZMM0,
        &TRITON_X86_REG_ZMM1,
        &TRITON_X86_REG_ZMM2,
        &TRITON_X86_REG_ZMM3,
        &TRITON_X86_REG_ZMM4,
        &TRITON_X86_REG_ZMM5,
        &TRITON_X86_REG_ZMM6,
        &TRITON_X86_REG_ZMM7,
        &TRITON_X86_REG_ZMM8,
        &TRITON_X86_REG_ZMM9,
        &TRITON_X86_REG_ZMM10,
        &TRITON_X86_REG_ZMM11,
        &TRITON_X86_REG_ZMM12,
        &TRITON_X86_REG_ZMM13,
        &TRITON_X86_REG_ZMM14,
        &TRITON_X86_REG_ZMM15,
        &TRITON_X86_REG_ZMM16,
        &TRITON_X86_REG_ZMM17,
        &TRITON_X86_REG_ZMM18,
        &TRITON_X86_REG_ZMM19,
        &TRITON_X86_REG_ZMM20,
        &TRITON_X86_REG_ZMM21,
        &TRITON_X86_REG_ZMM22,
        &TRITON_X86_REG_ZMM23,
        &TRITON_X86_REG_ZMM24,
        &TRITON_X86_REG_ZMM25,
        &TRITON_X86_REG_ZMM26,
        &TRITON_X86_REG_ZMM27,
        &TRITON_X86_REG_ZMM28,
        &TRITON_X86_REG_ZMM29,
        &TRITON_X86_REG_ZMM30,
        &TRITON_X86_REG_ZMM31,
        &TRITON_X86_REG_MXCSR,
        &TRITON_X86_REG_CR0,
        &TRITON_X86_REG_CR1,
        &TRITON_X86_REG_CR2,
        &TRITON_X86_REG_CR3,
        &TRITON_X86_REG_CR4,
        &TRITON_X86_REG_CR5,
        &TRITON_X86_REG_CR6,
        &TRITON_X86_REG_CR7,
        &TRITON_X86_REG_CR8,
        &TRITON_X86_REG_CR9,
        &TRITON_X86_REG_CR10,
        &TRITON_X86_REG_CR11,
        &TRITON_X86_REG_CR12,
        &TRITON_X86_REG_CR13,
        &TRITON_X86_REG_CR14,
        &TRITON_X86_REG_CR15,
        &TRITON_X86_REG_IE,
        &TRITON_X86_REG_DE,
        &TRITON_X86_REG_ZE,
        &TRITON_X86_REG_OE,
        &TRITON_X86_REG_UE,
        &TRITON_X86_REG_PE,
        &TRITON_X86_REG_DAZ,
        &TRITON_X86_REG_IM,
        &TRITON_X86_REG_DM,
        &TRITON_X86_REG_ZM,
        &TRITON_X86_REG_OM,
        &TRITON_X86_REG_UM,
        &TRITON_X86_REG_PM,
        &TRITON_X86_REG_RL,
        &TRITON_X86_REG_RH,
        &TRITON_X86_REG_FZ,
        &TRITON_X86_REG_AF,
        &TRITON_X86_REG_CF,
        &TRITON_X86_REG_DF,
        &TRITON_X86_REG_IF,
        &TRITON_X86_REG_OF,
        &TRITON_X86_REG_PF,
        &TRITON_X86_REG_SF,
        &TRITON_X86_REG_TF,
        &TRITON_X86_REG_ZF,
        &TRITON_X86_REG_CS,
        &TRITON_X86_REG_DS,
        &TRITON_X86_REG_ES,
        &TRITON_X86_REG_FS,
        &TRITON_X86_REG_GS,
        &TRITON_X86_REG_SS
      };


      x86Specifications::x86Specifications() {
      }


      x86Specifications::~x86Specifications() {
      }


      triton::arch::RegisterSpecification x86Specifications::getX86RegisterSpecification(triton::uint32 arch, triton::uint32 regId) const {
        triton::arch::RegisterSpecification ret;

        if (arch != triton::arch::ARCH_X86 && arch != triton::arch::ARCH_X86_64)
          return ret;

        switch (regId) {

          case triton::arch::x86::ID_REG_RAX:
            ret.setName("rax");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_RAX);
            break;

          case triton::arch::x86::ID_REG_EAX:
            ret.setName("eax");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RAX : triton::arch::x86::ID_REG_EAX);
            break;

          case triton::arch::x86::ID_REG_AX:
            ret.setName("ax");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RAX : triton::arch::x86::ID_REG_EAX);
            break;

          case triton::arch::x86::ID_REG_AH:
            ret.setName("ah");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(BYTE_SIZE_BIT);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RAX : triton::arch::x86::ID_REG_EAX);
            break;

          case triton::arch::x86::ID_REG_AL:
            ret.setName("al");
            ret.setHigh(BYTE_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RAX : triton::arch::x86::ID_REG_EAX);
            break;

          case triton::arch::x86::ID_REG_RBX:
            ret.setName("rbx");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_RBX);
            break;

          case triton::arch::x86::ID_REG_EBX:
            ret.setName("ebx");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RBX : triton::arch::x86::ID_REG_EBX);
            break;

          case triton::arch::x86::ID_REG_BX:
            ret.setName("bx");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RBX : triton::arch::x86::ID_REG_EBX);
            break;

          case triton::arch::x86::ID_REG_BH:
            ret.setName("bh");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(BYTE_SIZE_BIT);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RBX : triton::arch::x86::ID_REG_EBX);
            break;

          case triton::arch::x86::ID_REG_BL:
            ret.setName("bl");
            ret.setHigh(BYTE_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RBX : triton::arch::x86::ID_REG_EBX);
            break;

          case triton::arch::x86::ID_REG_RCX:
            ret.setName("rcx");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_RCX);
            break;

          case triton::arch::x86::ID_REG_ECX:
            ret.setName("ecx");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RCX : triton::arch::x86::ID_REG_ECX);
            break;

          case triton::arch::x86::ID_REG_CX:
            ret.setName("cx");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RCX : triton::arch::x86::ID_REG_ECX);
            break;

          case triton::arch::x86::ID_REG_CH:
            ret.setName("ch");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(BYTE_SIZE_BIT);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RCX : triton::arch::x86::ID_REG_ECX);
            break;

          case triton::arch::x86::ID_REG_CL:
            ret.setName("cl");
            ret.setHigh(BYTE_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RCX : triton::arch::x86::ID_REG_ECX);
            break;

          case triton::arch::x86::ID_REG_RDX:
            ret.setName("rdx");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_RDX);
            break;

          case triton::arch::x86::ID_REG_EDX:
            ret.setName("edx");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RDX : triton::arch::x86::ID_REG_EDX);
            break;

          case triton::arch::x86::ID_REG_DX:
            ret.setName("dx");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RDX : triton::arch::x86::ID_REG_EDX);
            break;

          case triton::arch::x86::ID_REG_DH:
            ret.setName("dh");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(BYTE_SIZE_BIT);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RDX : triton::arch::x86::ID_REG_EDX);
            break;

          case triton::arch::x86::ID_REG_DL:
            ret.setName("dl");
            ret.setHigh(BYTE_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RDX : triton::arch::x86::ID_REG_EDX);
            break;

          case triton::arch::x86::ID_REG_RDI:
            ret.setName("rdi");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_RDI);
            break;

          case triton::arch::x86::ID_REG_EDI:
            ret.setName("edi");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RDI : triton::arch::x86::ID_REG_EDI);
            break;

          case triton::arch::x86::ID_REG_DI:
            ret.setName("di");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RDI : triton::arch::x86::ID_REG_EDI);
            break;

          case triton::arch::x86::ID_REG_DIL:
            ret.setName("dil");
            ret.setHigh(BYTE_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RDI : triton::arch::x86::ID_REG_EDI);
            break;

          case triton::arch::x86::ID_REG_RSI:
            ret.setName("rsi");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_RSI);
            break;

          case triton::arch::x86::ID_REG_ESI:
            ret.setName("esi");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RSI : triton::arch::x86::ID_REG_ESI);
            break;

          case triton::arch::x86::ID_REG_SI:
            ret.setName("si");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RSI : triton::arch::x86::ID_REG_ESI);
            break;

          case triton::arch::x86::ID_REG_SIL:
            ret.setName("sil");
            ret.setHigh(BYTE_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RSI : triton::arch::x86::ID_REG_ESI);
            break;

          case triton::arch::x86::ID_REG_RBP:
            ret.setName("rbp");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_RBP);
            break;

          case triton::arch::x86::ID_REG_EBP:
            ret.setName("ebp");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RBP : triton::arch::x86::ID_REG_EBP);
            break;

          case triton::arch::x86::ID_REG_BP:
            ret.setName("bp");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RBP : triton::arch::x86::ID_REG_EBP);
            break;

          case triton::arch::x86::ID_REG_BPL:
            ret.setName("bpl");
            ret.setHigh(BYTE_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RBP : triton::arch::x86::ID_REG_EBP);
            break;

          case triton::arch::x86::ID_REG_RSP:
            ret.setName("rsp");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_RSP);
            break;

          case triton::arch::x86::ID_REG_ESP:
            ret.setName("esp");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RSP : triton::arch::x86::ID_REG_ESP);
            break;

          case triton::arch::x86::ID_REG_SP:
            ret.setName("sp");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RSP : triton::arch::x86::ID_REG_ESP);
            break;

          case triton::arch::x86::ID_REG_SPL:
            ret.setName("spl");
            ret.setHigh(BYTE_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RSP : triton::arch::x86::ID_REG_ESP);
            break;

          case triton::arch::x86::ID_REG_RIP:
            ret.setName("rip");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_RIP);
            break;

          case triton::arch::x86::ID_REG_EIP:
            ret.setName("eip");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RIP : triton::arch::x86::ID_REG_EIP);
            break;

          case triton::arch::x86::ID_REG_IP:
            ret.setName("ip");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId((arch == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RIP : triton::arch::x86::ID_REG_EIP);
            break;

          case triton::arch::x86::ID_REG_EFLAGS:
            ret.setName("eflags");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_EFLAGS);
            break;

          case triton::arch::x86::ID_REG_R8:
            ret.setName("r8");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R8);
            break;

          case triton::arch::x86::ID_REG_R8D:
            ret.setName("r8d");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R8);
            break;

          case triton::arch::x86::ID_REG_R8W:
            ret.setName("r8w");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R8);
            break;

          case triton::arch::x86::ID_REG_R8B:
            ret.setName("r8b");
            ret.setHigh(BYTE_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R8);
            break;

          case triton::arch::x86::ID_REG_R9:
            ret.setName("r9");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R9);
            break;

          case triton::arch::x86::ID_REG_R9D:
            ret.setName("r9d");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R9);
            break;

          case triton::arch::x86::ID_REG_R9W:
            ret.setName("r9w");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R9);
            break;

          case triton::arch::x86::ID_REG_R9B:
            ret.setName("r9b");
            ret.setHigh(BYTE_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R9);
            break;

          case triton::arch::x86::ID_REG_R10:
            ret.setName("r10");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R10);
            break;

          case triton::arch::x86::ID_REG_R10D:
            ret.setName("r10d");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R10);
            break;

          case triton::arch::x86::ID_REG_R10W:
            ret.setName("r10w");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R10);
            break;

          case triton::arch::x86::ID_REG_R10B:
            ret.setName("r10b");
            ret.setHigh(BYTE_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R10);
            break;

          case triton::arch::x86::ID_REG_R11:
            ret.setName("r11");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R11);
            break;

          case triton::arch::x86::ID_REG_R11D:
            ret.setName("r11d");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R11);
            break;

          case triton::arch::x86::ID_REG_R11W:
            ret.setName("r11w");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R11);
            break;

          case triton::arch::x86::ID_REG_R11B:
            ret.setName("r11b");
            ret.setHigh(BYTE_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R11);
            break;

          case triton::arch::x86::ID_REG_R12:
            ret.setName("r12");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R12);
            break;

          case triton::arch::x86::ID_REG_R12D:
            ret.setName("r12d");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R12);
            break;

          case triton::arch::x86::ID_REG_R12W:
            ret.setName("r12w");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R12);
            break;

          case triton::arch::x86::ID_REG_R12B:
            ret.setName("r12b");
            ret.setHigh(BYTE_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R12);
            break;

          case triton::arch::x86::ID_REG_R13:
            ret.setName("r13");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R13);
            break;

          case triton::arch::x86::ID_REG_R13D:
            ret.setName("r13d");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R13);
            break;

          case triton::arch::x86::ID_REG_R13W:
            ret.setName("r13w");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R13);
            break;

          case triton::arch::x86::ID_REG_R13B:
            ret.setName("r13b");
            ret.setHigh(BYTE_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R13);
            break;

          case triton::arch::x86::ID_REG_R14:
            ret.setName("r14");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R14);
            break;

          case triton::arch::x86::ID_REG_R14D:
            ret.setName("r14d");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R14);
            break;

          case triton::arch::x86::ID_REG_R14W:
            ret.setName("r14w");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R14);
            break;

          case triton::arch::x86::ID_REG_R14B:
            ret.setName("r14b");
            ret.setHigh(BYTE_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R14);
            break;

          case triton::arch::x86::ID_REG_R15:
            ret.setName("r15");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R15);
            break;

          case triton::arch::x86::ID_REG_R15D:
            ret.setName("r15d");
            ret.setHigh(DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R15);
            break;

          case triton::arch::x86::ID_REG_R15W:
            ret.setName("r15w");
            ret.setHigh(WORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R15);
            break;

          case triton::arch::x86::ID_REG_R15B:
            ret.setName("r15b");
            ret.setHigh(BYTE_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_R15);
            break;

          case triton::arch::x86::ID_REG_MM0:
            ret.setName("mm0");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_MM0);
            break;

          case triton::arch::x86::ID_REG_MM1:
            ret.setName("mm1");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_MM1);
            break;

          case triton::arch::x86::ID_REG_MM2:
            ret.setName("mm2");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_MM2);
            break;

          case triton::arch::x86::ID_REG_MM3:
            ret.setName("mm3");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_MM3);
            break;

          case triton::arch::x86::ID_REG_MM4:
            ret.setName("mm4");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_MM4);
            break;

          case triton::arch::x86::ID_REG_MM5:
            ret.setName("mm5");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_MM5);
            break;

          case triton::arch::x86::ID_REG_MM6:
            ret.setName("mm6");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_MM6);
            break;

          case triton::arch::x86::ID_REG_MM7:
            ret.setName("mm7");
            ret.setHigh(QWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_MM7);
            break;

          case triton::arch::x86::ID_REG_XMM0:
            ret.setName("xmm0");
            ret.setHigh(DQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_XMM0);
            break;

          case triton::arch::x86::ID_REG_XMM1:
            ret.setName("xmm1");
            ret.setHigh(DQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_XMM1);
            break;

          case triton::arch::x86::ID_REG_XMM2:
            ret.setName("xmm2");
            ret.setHigh(DQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_XMM2);
            break;

          case triton::arch::x86::ID_REG_XMM3:
            ret.setName("xmm3");
            ret.setHigh(DQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_XMM3);
            break;

          case triton::arch::x86::ID_REG_XMM4:
            ret.setName("xmm4");
            ret.setHigh(DQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_XMM4);
            break;

          case triton::arch::x86::ID_REG_XMM5:
            ret.setName("xmm5");
            ret.setHigh(DQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_XMM5);
            break;

          case triton::arch::x86::ID_REG_XMM6:
            ret.setName("xmm6");
            ret.setHigh(DQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_XMM6);
            break;

          case triton::arch::x86::ID_REG_XMM7:
            ret.setName("xmm7");
            ret.setHigh(DQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_XMM7);
            break;

          case triton::arch::x86::ID_REG_XMM8:
            ret.setName("xmm8");
            ret.setHigh(DQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_XMM8);
            break;

          case triton::arch::x86::ID_REG_XMM9:
            ret.setName("xmm9");
            ret.setHigh(DQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_XMM9);
            break;

          case triton::arch::x86::ID_REG_XMM10:
            ret.setName("xmm10");
            ret.setHigh(DQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_XMM10);
            break;

          case triton::arch::x86::ID_REG_XMM11:
            ret.setName("xmm11");
            ret.setHigh(DQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_XMM11);
            break;

          case triton::arch::x86::ID_REG_XMM12:
            ret.setName("xmm12");
            ret.setHigh(DQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_XMM12);
            break;

          case triton::arch::x86::ID_REG_XMM13:
            ret.setName("xmm13");
            ret.setHigh(DQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_XMM13);
            break;

          case triton::arch::x86::ID_REG_XMM14:
            ret.setName("xmm14");
            ret.setHigh(DQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_XMM14);
            break;

          case triton::arch::x86::ID_REG_XMM15:
            ret.setName("xmm15");
            ret.setHigh(DQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_XMM15);
            break;

          case triton::arch::x86::ID_REG_YMM0:
            ret.setName("ymm0");
            ret.setHigh(QQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_YMM0);
            break;

          case triton::arch::x86::ID_REG_YMM1:
            ret.setName("ymm1");
            ret.setHigh(QQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_YMM1);
            break;

          case triton::arch::x86::ID_REG_YMM2:
            ret.setName("ymm2");
            ret.setHigh(QQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_YMM2);
            break;

          case triton::arch::x86::ID_REG_YMM3:
            ret.setName("ymm3");
            ret.setHigh(QQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_YMM3);
            break;

          case triton::arch::x86::ID_REG_YMM4:
            ret.setName("ymm4");
            ret.setHigh(QQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_YMM4);
            break;

          case triton::arch::x86::ID_REG_YMM5:
            ret.setName("ymm5");
            ret.setHigh(QQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_YMM5);
            break;

          case triton::arch::x86::ID_REG_YMM6:
            ret.setName("ymm6");
            ret.setHigh(QQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_YMM6);
            break;

          case triton::arch::x86::ID_REG_YMM7:
            ret.setName("ymm7");
            ret.setHigh(QQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_YMM7);
            break;

          case triton::arch::x86::ID_REG_YMM8:
            ret.setName("ymm8");
            ret.setHigh(QQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_YMM8);
            break;

          case triton::arch::x86::ID_REG_YMM9:
            ret.setName("ymm9");
            ret.setHigh(QQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_YMM9);
            break;

          case triton::arch::x86::ID_REG_YMM10:
            ret.setName("ymm10");
            ret.setHigh(QQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_YMM10);
            break;

          case triton::arch::x86::ID_REG_YMM11:
            ret.setName("ymm11");
            ret.setHigh(QQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_YMM11);
            break;

          case triton::arch::x86::ID_REG_YMM12:
            ret.setName("ymm12");
            ret.setHigh(QQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_YMM12);
            break;

          case triton::arch::x86::ID_REG_YMM13:
            ret.setName("ymm13");
            ret.setHigh(QQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_YMM13);
            break;

          case triton::arch::x86::ID_REG_YMM14:
            ret.setName("ymm14");
            ret.setHigh(QQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_YMM14);
            break;

          case triton::arch::x86::ID_REG_YMM15:
            ret.setName("ymm15");
            ret.setHigh(QQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_YMM15);
            break;

          case triton::arch::x86::ID_REG_ZMM0:
            ret.setName("zmm0");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM0);
            break;

          case triton::arch::x86::ID_REG_ZMM1:
            ret.setName("zmm1");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM1);
            break;

          case triton::arch::x86::ID_REG_ZMM2:
            ret.setName("zmm2");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM2);
            break;

          case triton::arch::x86::ID_REG_ZMM3:
            ret.setName("zmm3");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM3);
            break;

          case triton::arch::x86::ID_REG_ZMM4:
            ret.setName("zmm4");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM4);
            break;

          case triton::arch::x86::ID_REG_ZMM5:
            ret.setName("zmm5");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM5);
            break;

          case triton::arch::x86::ID_REG_ZMM6:
            ret.setName("zmm6");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM6);
            break;

          case triton::arch::x86::ID_REG_ZMM7:
            ret.setName("zmm7");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM7);
            break;

          case triton::arch::x86::ID_REG_ZMM8:
            ret.setName("zmm8");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM8);
            break;

          case triton::arch::x86::ID_REG_ZMM9:
            ret.setName("zmm9");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM9);
            break;

          case triton::arch::x86::ID_REG_ZMM10:
            ret.setName("zmm10");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM10);
            break;

          case triton::arch::x86::ID_REG_ZMM11:
            ret.setName("zmm11");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM11);
            break;

          case triton::arch::x86::ID_REG_ZMM12:
            ret.setName("zmm12");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM12);
            break;

          case triton::arch::x86::ID_REG_ZMM13:
            ret.setName("zmm13");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM13);
            break;

          case triton::arch::x86::ID_REG_ZMM14:
            ret.setName("zmm14");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM14);
            break;

          case triton::arch::x86::ID_REG_ZMM15:
            ret.setName("zmm15");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM15);
            break;

          case triton::arch::x86::ID_REG_ZMM16:
            ret.setName("zmm16");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM16);
            break;

          case triton::arch::x86::ID_REG_ZMM17:
            ret.setName("zmm17");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM17);
            break;

          case triton::arch::x86::ID_REG_ZMM18:
            ret.setName("zmm18");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM18);
            break;

          case triton::arch::x86::ID_REG_ZMM19:
            ret.setName("zmm19");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM19);
            break;

          case triton::arch::x86::ID_REG_ZMM20:
            ret.setName("zmm20");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM20);
            break;

          case triton::arch::x86::ID_REG_ZMM21:
            ret.setName("zmm21");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM21);
            break;

          case triton::arch::x86::ID_REG_ZMM22:
            ret.setName("zmm22");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM22);
            break;

          case triton::arch::x86::ID_REG_ZMM23:
            ret.setName("zmm23");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM23);
            break;

          case triton::arch::x86::ID_REG_ZMM24:
            ret.setName("zmm24");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM24);
            break;

          case triton::arch::x86::ID_REG_ZMM25:
            ret.setName("zmm25");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM25);
            break;

          case triton::arch::x86::ID_REG_ZMM26:
            ret.setName("zmm26");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM26);
            break;

          case triton::arch::x86::ID_REG_ZMM27:
            ret.setName("zmm27");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM27);
            break;

          case triton::arch::x86::ID_REG_ZMM28:
            ret.setName("zmm28");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM28);
            break;

          case triton::arch::x86::ID_REG_ZMM29:
            ret.setName("zmm29");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM29);
            break;

          case triton::arch::x86::ID_REG_ZMM30:
            ret.setName("zmm30");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM30);
            break;

          case triton::arch::x86::ID_REG_ZMM31:
            ret.setName("zmm31");
            ret.setHigh(DQQWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZMM31);
            break;

          case triton::arch::x86::ID_REG_MXCSR:
            ret.setName("mxcsr");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_MXCSR);
            break;

          case triton::arch::x86::ID_REG_CR0:
            ret.setName("cr0");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CR0);
            break;

          case triton::arch::x86::ID_REG_CR1:
            ret.setName("cr1");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CR1);
            break;

          case triton::arch::x86::ID_REG_CR2:
            ret.setName("cr2");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CR2);
            break;

          case triton::arch::x86::ID_REG_CR3:
            ret.setName("cr3");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CR3);
            break;

          case triton::arch::x86::ID_REG_CR4:
            ret.setName("cr4");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CR4);
            break;

          case triton::arch::x86::ID_REG_CR5:
            ret.setName("cr5");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CR5);
            break;

          case triton::arch::x86::ID_REG_CR6:
            ret.setName("cr6");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CR6);
            break;

          case triton::arch::x86::ID_REG_CR7:
            ret.setName("cr7");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CR7);
            break;

          case triton::arch::x86::ID_REG_CR8:
            ret.setName("cr8");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CR8);
            break;

          case triton::arch::x86::ID_REG_CR9:
            ret.setName("cr9");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CR9);
            break;

          case triton::arch::x86::ID_REG_CR10:
            ret.setName("cr10");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CR10);
            break;

          case triton::arch::x86::ID_REG_CR11:
            ret.setName("cr11");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CR11);
            break;

          case triton::arch::x86::ID_REG_CR12:
            ret.setName("cr12");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CR12);
            break;

          case triton::arch::x86::ID_REG_CR13:
            ret.setName("cr13");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CR13);
            break;

          case triton::arch::x86::ID_REG_CR14:
            ret.setName("cr14");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CR14);
            break;

          case triton::arch::x86::ID_REG_CR15:
            ret.setName("cr15");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CR15);
            break;

          case triton::arch::x86::ID_REG_IE:
            ret.setName("ie");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_IE);
            break;

          case triton::arch::x86::ID_REG_DE:
            ret.setName("de");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_DE);
            break;

          case triton::arch::x86::ID_REG_ZE:
            ret.setName("ze");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZE);
            break;

          case triton::arch::x86::ID_REG_OE:
            ret.setName("oe");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_OE);
            break;

          case triton::arch::x86::ID_REG_UE:
            ret.setName("ue");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_UE);
            break;

          case triton::arch::x86::ID_REG_PE:
            ret.setName("pe");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_PE);
            break;

          case triton::arch::x86::ID_REG_DAZ:
            ret.setName("da");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_DAZ);
            break;

          case triton::arch::x86::ID_REG_IM:
            ret.setName("im");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_IM);
            break;

          case triton::arch::x86::ID_REG_DM:
            ret.setName("dm");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_DM);
            break;

          case triton::arch::x86::ID_REG_ZM:
            ret.setName("zm");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZM);
            break;

          case triton::arch::x86::ID_REG_OM:
            ret.setName("om");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_OM);
            break;

          case triton::arch::x86::ID_REG_UM:
            ret.setName("um");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_UM);
            break;

          case triton::arch::x86::ID_REG_PM:
            ret.setName("pm");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_PM);
            break;

          case triton::arch::x86::ID_REG_RL:
            ret.setName("rl");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_RL);
            break;

          case triton::arch::x86::ID_REG_RH:
            ret.setName("rh");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_RH);
            break;

          case triton::arch::x86::ID_REG_FZ:
            ret.setName("fz");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_FZ);
            break;

          case triton::arch::x86::ID_REG_AF:
            ret.setName("af");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_AF);
            break;

          case triton::arch::x86::ID_REG_CF:
            ret.setName("cf");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CF);
            break;

          case triton::arch::x86::ID_REG_DF:
            ret.setName("df");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_DF);
            break;

          case triton::arch::x86::ID_REG_IF:
            ret.setName("if");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_IF);
            break;

          case triton::arch::x86::ID_REG_OF:
            ret.setName("of");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_OF);
            break;

          case triton::arch::x86::ID_REG_PF:
            ret.setName("pf");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_PF);
            break;

          case triton::arch::x86::ID_REG_SF:
            ret.setName("sf");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_SF);
            break;

          case triton::arch::x86::ID_REG_TF:
            ret.setName("tf");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_TF);
            break;

          case triton::arch::x86::ID_REG_ZF:
            ret.setName("zf");
            ret.setHigh(0);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ZF);
            break;

          case triton::arch::x86::ID_REG_CS:
            ret.setName("cs");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_CS);
            break;

          case triton::arch::x86::ID_REG_DS:
            ret.setName("ds");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_DS);
            break;

          case triton::arch::x86::ID_REG_ES:
            ret.setName("es");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_ES);
            break;

          case triton::arch::x86::ID_REG_FS:
            ret.setName("fs");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_FS);
            break;

          case triton::arch::x86::ID_REG_GS:
            ret.setName("gs");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_GS);
            break;

          case triton::arch::x86::ID_REG_SS:
            ret.setName("ss");
            ret.setHigh((arch == triton::arch::ARCH_X86_64) ? QWORD_SIZE_BIT-1 : DWORD_SIZE_BIT-1);
            ret.setLow(0);
            ret.setParentId(triton::arch::x86::ID_REG_SS);
            break;

        }
        return ret;
      }


      triton::uint32 x86Specifications::capstoneRegisterToTritonRegister(triton::uint32 id) const {
        triton::uint32 tritonId = triton::arch::x86::ID_REG_INVALID;

        switch (id) {

          case triton::extlibs::capstone::X86_REG_RAX:
            tritonId = triton::arch::x86::ID_REG_RAX;
            break;

          case triton::extlibs::capstone::X86_REG_EAX:
            tritonId = triton::arch::x86::ID_REG_EAX;
            break;

          case triton::extlibs::capstone::X86_REG_AX:
            tritonId = triton::arch::x86::ID_REG_AX;
            break;

          case triton::extlibs::capstone::X86_REG_AH:
            tritonId = triton::arch::x86::ID_REG_AH;
            break;

          case triton::extlibs::capstone::X86_REG_AL:
            tritonId = triton::arch::x86::ID_REG_AL;
            break;

          case triton::extlibs::capstone::X86_REG_RBX:
            tritonId = triton::arch::x86::ID_REG_RBX;
            break;

          case triton::extlibs::capstone::X86_REG_EBX:
            tritonId = triton::arch::x86::ID_REG_EBX;
            break;

          case triton::extlibs::capstone::X86_REG_BX:
            tritonId = triton::arch::x86::ID_REG_BX;
            break;

          case triton::extlibs::capstone::X86_REG_BH:
            tritonId = triton::arch::x86::ID_REG_BH;
            break;

          case triton::extlibs::capstone::X86_REG_BL:
            tritonId = triton::arch::x86::ID_REG_BL;
            break;

          case triton::extlibs::capstone::X86_REG_RCX:
            tritonId = triton::arch::x86::ID_REG_RCX;
            break;

          case triton::extlibs::capstone::X86_REG_ECX:
            tritonId = triton::arch::x86::ID_REG_ECX;
            break;

          case triton::extlibs::capstone::X86_REG_CX:
            tritonId = triton::arch::x86::ID_REG_CX;
            break;

          case triton::extlibs::capstone::X86_REG_CH:
            tritonId = triton::arch::x86::ID_REG_CH;
            break;

          case triton::extlibs::capstone::X86_REG_CL:
            tritonId = triton::arch::x86::ID_REG_CL;
            break;

          case triton::extlibs::capstone::X86_REG_RDX:
            tritonId = triton::arch::x86::ID_REG_RDX;
            break;

          case triton::extlibs::capstone::X86_REG_EDX:
            tritonId = triton::arch::x86::ID_REG_EDX;
            break;

          case triton::extlibs::capstone::X86_REG_DX:
            tritonId = triton::arch::x86::ID_REG_DX;
            break;

          case triton::extlibs::capstone::X86_REG_DH:
            tritonId = triton::arch::x86::ID_REG_DH;
            break;

          case triton::extlibs::capstone::X86_REG_DL:
            tritonId = triton::arch::x86::ID_REG_DL;
            break;

          case triton::extlibs::capstone::X86_REG_RDI:
            tritonId = triton::arch::x86::ID_REG_RDI;
            break;

          case triton::extlibs::capstone::X86_REG_EDI:
            tritonId = triton::arch::x86::ID_REG_EDI;
            break;

          case triton::extlibs::capstone::X86_REG_DI:
            tritonId = triton::arch::x86::ID_REG_DI;
            break;

          case triton::extlibs::capstone::X86_REG_DIL:
            tritonId = triton::arch::x86::ID_REG_DIL;
            break;

          case triton::extlibs::capstone::X86_REG_RSI:
            tritonId = triton::arch::x86::ID_REG_RSI;
            break;

          case triton::extlibs::capstone::X86_REG_ESI:
            tritonId = triton::arch::x86::ID_REG_ESI;
            break;

          case triton::extlibs::capstone::X86_REG_SI:
            tritonId = triton::arch::x86::ID_REG_SI;
            break;

          case triton::extlibs::capstone::X86_REG_SIL:
            tritonId = triton::arch::x86::ID_REG_SIL;
            break;

          case triton::extlibs::capstone::X86_REG_RBP:
            tritonId = triton::arch::x86::ID_REG_RBP;
            break;

          case triton::extlibs::capstone::X86_REG_EBP:
            tritonId = triton::arch::x86::ID_REG_EBP;
            break;

          case triton::extlibs::capstone::X86_REG_BP:
            tritonId = triton::arch::x86::ID_REG_BP;
            break;

          case triton::extlibs::capstone::X86_REG_BPL:
            tritonId = triton::arch::x86::ID_REG_BPL;
            break;

          case triton::extlibs::capstone::X86_REG_RSP:
            tritonId = triton::arch::x86::ID_REG_RSP;
            break;

          case triton::extlibs::capstone::X86_REG_ESP:
            tritonId = triton::arch::x86::ID_REG_ESP;
            break;

          case triton::extlibs::capstone::X86_REG_SP:
            tritonId = triton::arch::x86::ID_REG_SP;
            break;

          case triton::extlibs::capstone::X86_REG_SPL:
            tritonId = triton::arch::x86::ID_REG_SPL;
            break;

          case triton::extlibs::capstone::X86_REG_RIP:
            tritonId = triton::arch::x86::ID_REG_RIP;
            break;

          case triton::extlibs::capstone::X86_REG_EIP:
            tritonId = triton::arch::x86::ID_REG_EIP;
            break;

          case triton::extlibs::capstone::X86_REG_IP:
            tritonId = triton::arch::x86::ID_REG_IP;
            break;

          case triton::extlibs::capstone::X86_REG_EFLAGS:
            tritonId = triton::arch::x86::ID_REG_EFLAGS;
            break;

          case triton::extlibs::capstone::X86_REG_R8:
            tritonId = triton::arch::x86::ID_REG_R8;
            break;

          case triton::extlibs::capstone::X86_REG_R8D:
            tritonId = triton::arch::x86::ID_REG_R8D;
            break;

          case triton::extlibs::capstone::X86_REG_R8W:
            tritonId = triton::arch::x86::ID_REG_R8W;
            break;

          case triton::extlibs::capstone::X86_REG_R8B:
            tritonId = triton::arch::x86::ID_REG_R8B;
            break;

          case triton::extlibs::capstone::X86_REG_R9:
            tritonId = triton::arch::x86::ID_REG_R9;
            break;

          case triton::extlibs::capstone::X86_REG_R9D:
            tritonId = triton::arch::x86::ID_REG_R9D;
            break;

          case triton::extlibs::capstone::X86_REG_R9W:
            tritonId = triton::arch::x86::ID_REG_R9W;
            break;

          case triton::extlibs::capstone::X86_REG_R9B:
            tritonId = triton::arch::x86::ID_REG_R9B;
            break;

          case triton::extlibs::capstone::X86_REG_R10:
            tritonId = triton::arch::x86::ID_REG_R10;
            break;

          case triton::extlibs::capstone::X86_REG_R10D:
            tritonId = triton::arch::x86::ID_REG_R10D;
            break;

          case triton::extlibs::capstone::X86_REG_R10W:
            tritonId = triton::arch::x86::ID_REG_R10W;
            break;

          case triton::extlibs::capstone::X86_REG_R10B:
            tritonId = triton::arch::x86::ID_REG_R10B;
            break;

          case triton::extlibs::capstone::X86_REG_R11:
            tritonId = triton::arch::x86::ID_REG_R11;
            break;

          case triton::extlibs::capstone::X86_REG_R11D:
            tritonId = triton::arch::x86::ID_REG_R11D;
            break;

          case triton::extlibs::capstone::X86_REG_R11W:
            tritonId = triton::arch::x86::ID_REG_R11W;
            break;

          case triton::extlibs::capstone::X86_REG_R11B:
            tritonId = triton::arch::x86::ID_REG_R11B;
            break;

          case triton::extlibs::capstone::X86_REG_R12:
            tritonId = triton::arch::x86::ID_REG_R12;
            break;

          case triton::extlibs::capstone::X86_REG_R12D:
            tritonId = triton::arch::x86::ID_REG_R12D;
            break;

          case triton::extlibs::capstone::X86_REG_R12W:
            tritonId = triton::arch::x86::ID_REG_R12W;
            break;

          case triton::extlibs::capstone::X86_REG_R12B:
            tritonId = triton::arch::x86::ID_REG_R12B;
            break;

          case triton::extlibs::capstone::X86_REG_R13:
            tritonId = triton::arch::x86::ID_REG_R13;
            break;

          case triton::extlibs::capstone::X86_REG_R13D:
            tritonId = triton::arch::x86::ID_REG_R13D;
            break;

          case triton::extlibs::capstone::X86_REG_R13W:
            tritonId = triton::arch::x86::ID_REG_R13W;
            break;

          case triton::extlibs::capstone::X86_REG_R13B:
            tritonId = triton::arch::x86::ID_REG_R13B;
            break;

          case triton::extlibs::capstone::X86_REG_R14:
            tritonId = triton::arch::x86::ID_REG_R14;
            break;

          case triton::extlibs::capstone::X86_REG_R14D:
            tritonId = triton::arch::x86::ID_REG_R14D;
            break;

          case triton::extlibs::capstone::X86_REG_R14W:
            tritonId = triton::arch::x86::ID_REG_R14W;
            break;

          case triton::extlibs::capstone::X86_REG_R14B:
            tritonId = triton::arch::x86::ID_REG_R14B;
            break;

          case triton::extlibs::capstone::X86_REG_R15:
            tritonId = triton::arch::x86::ID_REG_R15;
            break;

          case triton::extlibs::capstone::X86_REG_R15D:
            tritonId = triton::arch::x86::ID_REG_R15D;
            break;

          case triton::extlibs::capstone::X86_REG_R15W:
            tritonId = triton::arch::x86::ID_REG_R15W;
            break;

          case triton::extlibs::capstone::X86_REG_R15B:
            tritonId = triton::arch::x86::ID_REG_R15B;
            break;

          case triton::extlibs::capstone::X86_REG_MM0:
            tritonId = triton::arch::x86::ID_REG_MM0;
            break;

          case triton::extlibs::capstone::X86_REG_MM1:
            tritonId = triton::arch::x86::ID_REG_MM1;
            break;

          case triton::extlibs::capstone::X86_REG_MM2:
            tritonId = triton::arch::x86::ID_REG_MM2;
            break;

          case triton::extlibs::capstone::X86_REG_MM3:
            tritonId = triton::arch::x86::ID_REG_MM3;
            break;

          case triton::extlibs::capstone::X86_REG_MM4:
            tritonId = triton::arch::x86::ID_REG_MM4;
            break;

          case triton::extlibs::capstone::X86_REG_MM5:
            tritonId = triton::arch::x86::ID_REG_MM5;
            break;

          case triton::extlibs::capstone::X86_REG_MM6:
            tritonId = triton::arch::x86::ID_REG_MM6;
            break;

          case triton::extlibs::capstone::X86_REG_MM7:
            tritonId = triton::arch::x86::ID_REG_MM7;
            break;

          case triton::extlibs::capstone::X86_REG_XMM0:
            tritonId = triton::arch::x86::ID_REG_XMM0;
            break;

          case triton::extlibs::capstone::X86_REG_XMM1:
            tritonId = triton::arch::x86::ID_REG_XMM1;
            break;

          case triton::extlibs::capstone::X86_REG_XMM2:
            tritonId = triton::arch::x86::ID_REG_XMM2;
            break;

          case triton::extlibs::capstone::X86_REG_XMM3:
            tritonId = triton::arch::x86::ID_REG_XMM3;
            break;

          case triton::extlibs::capstone::X86_REG_XMM4:
            tritonId = triton::arch::x86::ID_REG_XMM4;
            break;

          case triton::extlibs::capstone::X86_REG_XMM5:
            tritonId = triton::arch::x86::ID_REG_XMM5;
            break;

          case triton::extlibs::capstone::X86_REG_XMM6:
            tritonId = triton::arch::x86::ID_REG_XMM6;
            break;

          case triton::extlibs::capstone::X86_REG_XMM7:
            tritonId = triton::arch::x86::ID_REG_XMM7;
            break;

          case triton::extlibs::capstone::X86_REG_XMM8:
            tritonId = triton::arch::x86::ID_REG_XMM8;
            break;

          case triton::extlibs::capstone::X86_REG_XMM9:
            tritonId = triton::arch::x86::ID_REG_XMM9;
            break;

          case triton::extlibs::capstone::X86_REG_XMM10:
            tritonId = triton::arch::x86::ID_REG_XMM10;
            break;

          case triton::extlibs::capstone::X86_REG_XMM11:
            tritonId = triton::arch::x86::ID_REG_XMM11;
            break;

          case triton::extlibs::capstone::X86_REG_XMM12:
            tritonId = triton::arch::x86::ID_REG_XMM12;
            break;

          case triton::extlibs::capstone::X86_REG_XMM13:
            tritonId = triton::arch::x86::ID_REG_XMM13;
            break;

          case triton::extlibs::capstone::X86_REG_XMM14:
            tritonId = triton::arch::x86::ID_REG_XMM14;
            break;

          case triton::extlibs::capstone::X86_REG_XMM15:
            tritonId = triton::arch::x86::ID_REG_XMM15;
            break;

          case triton::extlibs::capstone::X86_REG_YMM0:
            tritonId = triton::arch::x86::ID_REG_YMM0;
            break;

          case triton::extlibs::capstone::X86_REG_YMM1:
            tritonId = triton::arch::x86::ID_REG_YMM1;
            break;

          case triton::extlibs::capstone::X86_REG_YMM2:
            tritonId = triton::arch::x86::ID_REG_YMM2;
            break;

          case triton::extlibs::capstone::X86_REG_YMM3:
            tritonId = triton::arch::x86::ID_REG_YMM3;
            break;

          case triton::extlibs::capstone::X86_REG_YMM4:
            tritonId = triton::arch::x86::ID_REG_YMM4;
            break;

          case triton::extlibs::capstone::X86_REG_YMM5:
            tritonId = triton::arch::x86::ID_REG_YMM5;
            break;

          case triton::extlibs::capstone::X86_REG_YMM6:
            tritonId = triton::arch::x86::ID_REG_YMM6;
            break;

          case triton::extlibs::capstone::X86_REG_YMM7:
            tritonId = triton::arch::x86::ID_REG_YMM7;
            break;

          case triton::extlibs::capstone::X86_REG_YMM8:
            tritonId = triton::arch::x86::ID_REG_YMM8;
            break;

          case triton::extlibs::capstone::X86_REG_YMM9:
            tritonId = triton::arch::x86::ID_REG_YMM9;
            break;

          case triton::extlibs::capstone::X86_REG_YMM10:
            tritonId = triton::arch::x86::ID_REG_YMM10;
            break;

          case triton::extlibs::capstone::X86_REG_YMM11:
            tritonId = triton::arch::x86::ID_REG_YMM11;
            break;

          case triton::extlibs::capstone::X86_REG_YMM12:
            tritonId = triton::arch::x86::ID_REG_YMM12;
            break;

          case triton::extlibs::capstone::X86_REG_YMM13:
            tritonId = triton::arch::x86::ID_REG_YMM13;
            break;

          case triton::extlibs::capstone::X86_REG_YMM14:
            tritonId = triton::arch::x86::ID_REG_YMM14;
            break;

          case triton::extlibs::capstone::X86_REG_YMM15:
            tritonId = triton::arch::x86::ID_REG_YMM15;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM0:
            tritonId = triton::arch::x86::ID_REG_ZMM0;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM1:
            tritonId = triton::arch::x86::ID_REG_ZMM1;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM2:
            tritonId = triton::arch::x86::ID_REG_ZMM2;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM3:
            tritonId = triton::arch::x86::ID_REG_ZMM3;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM4:
            tritonId = triton::arch::x86::ID_REG_ZMM4;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM5:
            tritonId = triton::arch::x86::ID_REG_ZMM5;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM6:
            tritonId = triton::arch::x86::ID_REG_ZMM6;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM7:
            tritonId = triton::arch::x86::ID_REG_ZMM7;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM8:
            tritonId = triton::arch::x86::ID_REG_ZMM8;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM9:
            tritonId = triton::arch::x86::ID_REG_ZMM9;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM10:
            tritonId = triton::arch::x86::ID_REG_ZMM10;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM11:
            tritonId = triton::arch::x86::ID_REG_ZMM11;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM12:
            tritonId = triton::arch::x86::ID_REG_ZMM12;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM13:
            tritonId = triton::arch::x86::ID_REG_ZMM13;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM14:
            tritonId = triton::arch::x86::ID_REG_ZMM14;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM15:
            tritonId = triton::arch::x86::ID_REG_ZMM15;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM16:
            tritonId = triton::arch::x86::ID_REG_ZMM16;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM17:
            tritonId = triton::arch::x86::ID_REG_ZMM17;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM18:
            tritonId = triton::arch::x86::ID_REG_ZMM18;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM19:
            tritonId = triton::arch::x86::ID_REG_ZMM19;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM20:
            tritonId = triton::arch::x86::ID_REG_ZMM20;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM21:
            tritonId = triton::arch::x86::ID_REG_ZMM21;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM22:
            tritonId = triton::arch::x86::ID_REG_ZMM22;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM23:
            tritonId = triton::arch::x86::ID_REG_ZMM23;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM24:
            tritonId = triton::arch::x86::ID_REG_ZMM24;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM25:
            tritonId = triton::arch::x86::ID_REG_ZMM25;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM26:
            tritonId = triton::arch::x86::ID_REG_ZMM26;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM27:
            tritonId = triton::arch::x86::ID_REG_ZMM27;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM28:
            tritonId = triton::arch::x86::ID_REG_ZMM28;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM29:
            tritonId = triton::arch::x86::ID_REG_ZMM29;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM30:
            tritonId = triton::arch::x86::ID_REG_ZMM30;
            break;

          case triton::extlibs::capstone::X86_REG_ZMM31:
            tritonId = triton::arch::x86::ID_REG_ZMM31;
            break;

          case triton::extlibs::capstone::X86_REG_CR0:
            tritonId = triton::arch::x86::ID_REG_CR0;
            break;

          case triton::extlibs::capstone::X86_REG_CR1:
            tritonId = triton::arch::x86::ID_REG_CR1;
            break;

          case triton::extlibs::capstone::X86_REG_CR2:
            tritonId = triton::arch::x86::ID_REG_CR2;
            break;

          case triton::extlibs::capstone::X86_REG_CR3:
            tritonId = triton::arch::x86::ID_REG_CR3;
            break;

          case triton::extlibs::capstone::X86_REG_CR4:
            tritonId = triton::arch::x86::ID_REG_CR4;
            break;

          case triton::extlibs::capstone::X86_REG_CR5:
            tritonId = triton::arch::x86::ID_REG_CR5;
            break;

          case triton::extlibs::capstone::X86_REG_CR6:
            tritonId = triton::arch::x86::ID_REG_CR6;
            break;

          case triton::extlibs::capstone::X86_REG_CR7:
            tritonId = triton::arch::x86::ID_REG_CR7;
            break;

          case triton::extlibs::capstone::X86_REG_CR8:
            tritonId = triton::arch::x86::ID_REG_CR8;
            break;

          case triton::extlibs::capstone::X86_REG_CR9:
            tritonId = triton::arch::x86::ID_REG_CR9;
            break;

          case triton::extlibs::capstone::X86_REG_CR10:
            tritonId = triton::arch::x86::ID_REG_CR10;
            break;

          case triton::extlibs::capstone::X86_REG_CR11:
            tritonId = triton::arch::x86::ID_REG_CR11;
            break;

          case triton::extlibs::capstone::X86_REG_CR12:
            tritonId = triton::arch::x86::ID_REG_CR12;
            break;

          case triton::extlibs::capstone::X86_REG_CR13:
            tritonId = triton::arch::x86::ID_REG_CR13;
            break;

          case triton::extlibs::capstone::X86_REG_CR14:
            tritonId = triton::arch::x86::ID_REG_CR14;
            break;

          case triton::extlibs::capstone::X86_REG_CR15:
            tritonId = triton::arch::x86::ID_REG_CR15;
            break;

          case triton::extlibs::capstone::X86_REG_CS:
            tritonId = triton::arch::x86::ID_REG_CS;
            break;

          case triton::extlibs::capstone::X86_REG_DS:
            tritonId = triton::arch::x86::ID_REG_DS;
            break;

          case triton::extlibs::capstone::X86_REG_ES:
            tritonId = triton::arch::x86::ID_REG_ES;
            break;

          case triton::extlibs::capstone::X86_REG_FS:
            tritonId = triton::arch::x86::ID_REG_FS;
            break;

          case triton::extlibs::capstone::X86_REG_GS:
            tritonId = triton::arch::x86::ID_REG_GS;
            break;

          case triton::extlibs::capstone::X86_REG_SS:
            tritonId = triton::arch::x86::ID_REG_SS;
            break;

          default:
            tritonId = triton::arch::x86::ID_REG_INVALID;
            break;

        }
        return tritonId;
      }


      triton::uint32 x86Specifications::capstoneInstructionToTritonInstruction(triton::uint32 id) const {
        triton::uint32 tritonId = triton::arch::x86::ID_INST_INVALID;

        switch (id) {

          case triton::extlibs::capstone::X86_INS_INVALID:
            tritonId = triton::arch::x86::ID_INST_INVALID;
            break;

          case triton::extlibs::capstone::X86_INS_AAA:
            tritonId = triton::arch::x86::ID_INS_AAA;
            break;

          case triton::extlibs::capstone::X86_INS_AAD:
            tritonId = triton::arch::x86::ID_INS_AAD;
            break;

          case triton::extlibs::capstone::X86_INS_AAM:
            tritonId = triton::arch::x86::ID_INS_AAM;
            break;

          case triton::extlibs::capstone::X86_INS_AAS:
            tritonId = triton::arch::x86::ID_INS_AAS;
            break;

          case triton::extlibs::capstone::X86_INS_FABS:
            tritonId = triton::arch::x86::ID_INS_FABS;
            break;

          case triton::extlibs::capstone::X86_INS_ADC:
            tritonId = triton::arch::x86::ID_INS_ADC;
            break;

          case triton::extlibs::capstone::X86_INS_ADCX:
            tritonId = triton::arch::x86::ID_INS_ADCX;
            break;

          case triton::extlibs::capstone::X86_INS_ADD:
            tritonId = triton::arch::x86::ID_INS_ADD;
            break;

          case triton::extlibs::capstone::X86_INS_ADDPD:
            tritonId = triton::arch::x86::ID_INS_ADDPD;
            break;

          case triton::extlibs::capstone::X86_INS_ADDPS:
            tritonId = triton::arch::x86::ID_INS_ADDPS;
            break;

          case triton::extlibs::capstone::X86_INS_ADDSD:
            tritonId = triton::arch::x86::ID_INS_ADDSD;
            break;

          case triton::extlibs::capstone::X86_INS_ADDSS:
            tritonId = triton::arch::x86::ID_INS_ADDSS;
            break;

          case triton::extlibs::capstone::X86_INS_ADDSUBPD:
            tritonId = triton::arch::x86::ID_INS_ADDSUBPD;
            break;

          case triton::extlibs::capstone::X86_INS_ADDSUBPS:
            tritonId = triton::arch::x86::ID_INS_ADDSUBPS;
            break;

          case triton::extlibs::capstone::X86_INS_FADD:
            tritonId = triton::arch::x86::ID_INS_FADD;
            break;

          case triton::extlibs::capstone::X86_INS_FIADD:
            tritonId = triton::arch::x86::ID_INS_FIADD;
            break;

          case triton::extlibs::capstone::X86_INS_FADDP:
            tritonId = triton::arch::x86::ID_INS_FADDP;
            break;

          case triton::extlibs::capstone::X86_INS_ADOX:
            tritonId = triton::arch::x86::ID_INS_ADOX;
            break;

          case triton::extlibs::capstone::X86_INS_AESDECLAST:
            tritonId = triton::arch::x86::ID_INS_AESDECLAST;
            break;

          case triton::extlibs::capstone::X86_INS_AESDEC:
            tritonId = triton::arch::x86::ID_INS_AESDEC;
            break;

          case triton::extlibs::capstone::X86_INS_AESENCLAST:
            tritonId = triton::arch::x86::ID_INS_AESENCLAST;
            break;

          case triton::extlibs::capstone::X86_INS_AESENC:
            tritonId = triton::arch::x86::ID_INS_AESENC;
            break;

          case triton::extlibs::capstone::X86_INS_AESIMC:
            tritonId = triton::arch::x86::ID_INS_AESIMC;
            break;

          case triton::extlibs::capstone::X86_INS_AESKEYGENASSIST:
            tritonId = triton::arch::x86::ID_INS_AESKEYGENASSIST;
            break;

          case triton::extlibs::capstone::X86_INS_AND:
            tritonId = triton::arch::x86::ID_INS_AND;
            break;

          case triton::extlibs::capstone::X86_INS_ANDN:
            tritonId = triton::arch::x86::ID_INS_ANDN;
            break;

          case triton::extlibs::capstone::X86_INS_ANDNPD:
            tritonId = triton::arch::x86::ID_INS_ANDNPD;
            break;

          case triton::extlibs::capstone::X86_INS_ANDNPS:
            tritonId = triton::arch::x86::ID_INS_ANDNPS;
            break;

          case triton::extlibs::capstone::X86_INS_ANDPD:
            tritonId = triton::arch::x86::ID_INS_ANDPD;
            break;

          case triton::extlibs::capstone::X86_INS_ANDPS:
            tritonId = triton::arch::x86::ID_INS_ANDPS;
            break;

          case triton::extlibs::capstone::X86_INS_ARPL:
            tritonId = triton::arch::x86::ID_INS_ARPL;
            break;

          case triton::extlibs::capstone::X86_INS_BEXTR:
            tritonId = triton::arch::x86::ID_INS_BEXTR;
            break;

          case triton::extlibs::capstone::X86_INS_BLCFILL:
            tritonId = triton::arch::x86::ID_INS_BLCFILL;
            break;

          case triton::extlibs::capstone::X86_INS_BLCI:
            tritonId = triton::arch::x86::ID_INS_BLCI;
            break;

          case triton::extlibs::capstone::X86_INS_BLCIC:
            tritonId = triton::arch::x86::ID_INS_BLCIC;
            break;

          case triton::extlibs::capstone::X86_INS_BLCMSK:
            tritonId = triton::arch::x86::ID_INS_BLCMSK;
            break;

          case triton::extlibs::capstone::X86_INS_BLCS:
            tritonId = triton::arch::x86::ID_INS_BLCS;
            break;

          case triton::extlibs::capstone::X86_INS_BLENDPD:
            tritonId = triton::arch::x86::ID_INS_BLENDPD;
            break;

          case triton::extlibs::capstone::X86_INS_BLENDPS:
            tritonId = triton::arch::x86::ID_INS_BLENDPS;
            break;

          case triton::extlibs::capstone::X86_INS_BLENDVPD:
            tritonId = triton::arch::x86::ID_INS_BLENDVPD;
            break;

          case triton::extlibs::capstone::X86_INS_BLENDVPS:
            tritonId = triton::arch::x86::ID_INS_BLENDVPS;
            break;

          case triton::extlibs::capstone::X86_INS_BLSFILL:
            tritonId = triton::arch::x86::ID_INS_BLSFILL;
            break;

          case triton::extlibs::capstone::X86_INS_BLSI:
            tritonId = triton::arch::x86::ID_INS_BLSI;
            break;

          case triton::extlibs::capstone::X86_INS_BLSIC:
            tritonId = triton::arch::x86::ID_INS_BLSIC;
            break;

          case triton::extlibs::capstone::X86_INS_BLSMSK:
            tritonId = triton::arch::x86::ID_INS_BLSMSK;
            break;

          case triton::extlibs::capstone::X86_INS_BLSR:
            tritonId = triton::arch::x86::ID_INS_BLSR;
            break;

          case triton::extlibs::capstone::X86_INS_BOUND:
            tritonId = triton::arch::x86::ID_INS_BOUND;
            break;

          case triton::extlibs::capstone::X86_INS_BSF:
            tritonId = triton::arch::x86::ID_INS_BSF;
            break;

          case triton::extlibs::capstone::X86_INS_BSR:
            tritonId = triton::arch::x86::ID_INS_BSR;
            break;

          case triton::extlibs::capstone::X86_INS_BSWAP:
            tritonId = triton::arch::x86::ID_INS_BSWAP;
            break;

          case triton::extlibs::capstone::X86_INS_BT:
            tritonId = triton::arch::x86::ID_INS_BT;
            break;

          case triton::extlibs::capstone::X86_INS_BTC:
            tritonId = triton::arch::x86::ID_INS_BTC;
            break;

          case triton::extlibs::capstone::X86_INS_BTR:
            tritonId = triton::arch::x86::ID_INS_BTR;
            break;

          case triton::extlibs::capstone::X86_INS_BTS:
            tritonId = triton::arch::x86::ID_INS_BTS;
            break;

          case triton::extlibs::capstone::X86_INS_BZHI:
            tritonId = triton::arch::x86::ID_INS_BZHI;
            break;

          case triton::extlibs::capstone::X86_INS_CALL:
            tritonId = triton::arch::x86::ID_INS_CALL;
            break;

          case triton::extlibs::capstone::X86_INS_CBW:
            tritonId = triton::arch::x86::ID_INS_CBW;
            break;

          case triton::extlibs::capstone::X86_INS_CDQ:
            tritonId = triton::arch::x86::ID_INS_CDQ;
            break;

          case triton::extlibs::capstone::X86_INS_CDQE:
            tritonId = triton::arch::x86::ID_INS_CDQE;
            break;

          case triton::extlibs::capstone::X86_INS_FCHS:
            tritonId = triton::arch::x86::ID_INS_FCHS;
            break;

          case triton::extlibs::capstone::X86_INS_CLAC:
            tritonId = triton::arch::x86::ID_INS_CLAC;
            break;

          case triton::extlibs::capstone::X86_INS_CLC:
            tritonId = triton::arch::x86::ID_INS_CLC;
            break;

          case triton::extlibs::capstone::X86_INS_CLD:
            tritonId = triton::arch::x86::ID_INS_CLD;
            break;

          case triton::extlibs::capstone::X86_INS_CLFLUSH:
            tritonId = triton::arch::x86::ID_INS_CLFLUSH;
            break;

          case triton::extlibs::capstone::X86_INS_CLGI:
            tritonId = triton::arch::x86::ID_INS_CLGI;
            break;

          case triton::extlibs::capstone::X86_INS_CLI:
            tritonId = triton::arch::x86::ID_INS_CLI;
            break;

          case triton::extlibs::capstone::X86_INS_CLTS:
            tritonId = triton::arch::x86::ID_INS_CLTS;
            break;

          case triton::extlibs::capstone::X86_INS_CMC:
            tritonId = triton::arch::x86::ID_INS_CMC;
            break;

          case triton::extlibs::capstone::X86_INS_CMOVA:
            tritonId = triton::arch::x86::ID_INS_CMOVA;
            break;

          case triton::extlibs::capstone::X86_INS_CMOVAE:
            tritonId = triton::arch::x86::ID_INS_CMOVAE;
            break;

          case triton::extlibs::capstone::X86_INS_CMOVB:
            tritonId = triton::arch::x86::ID_INS_CMOVB;
            break;

          case triton::extlibs::capstone::X86_INS_CMOVBE:
            tritonId = triton::arch::x86::ID_INS_CMOVBE;
            break;

          case triton::extlibs::capstone::X86_INS_FCMOVBE:
            tritonId = triton::arch::x86::ID_INS_FCMOVBE;
            break;

          case triton::extlibs::capstone::X86_INS_FCMOVB:
            tritonId = triton::arch::x86::ID_INS_FCMOVB;
            break;

          case triton::extlibs::capstone::X86_INS_CMOVE:
            tritonId = triton::arch::x86::ID_INS_CMOVE;
            break;

          case triton::extlibs::capstone::X86_INS_FCMOVE:
            tritonId = triton::arch::x86::ID_INS_FCMOVE;
            break;

          case triton::extlibs::capstone::X86_INS_CMOVG:
            tritonId = triton::arch::x86::ID_INS_CMOVG;
            break;

          case triton::extlibs::capstone::X86_INS_CMOVGE:
            tritonId = triton::arch::x86::ID_INS_CMOVGE;
            break;

          case triton::extlibs::capstone::X86_INS_CMOVL:
            tritonId = triton::arch::x86::ID_INS_CMOVL;
            break;

          case triton::extlibs::capstone::X86_INS_CMOVLE:
            tritonId = triton::arch::x86::ID_INS_CMOVLE;
            break;

          case triton::extlibs::capstone::X86_INS_FCMOVNBE:
            tritonId = triton::arch::x86::ID_INS_FCMOVNBE;
            break;

          case triton::extlibs::capstone::X86_INS_FCMOVNB:
            tritonId = triton::arch::x86::ID_INS_FCMOVNB;
            break;

          case triton::extlibs::capstone::X86_INS_CMOVNE:
            tritonId = triton::arch::x86::ID_INS_CMOVNE;
            break;

          case triton::extlibs::capstone::X86_INS_FCMOVNE:
            tritonId = triton::arch::x86::ID_INS_FCMOVNE;
            break;

          case triton::extlibs::capstone::X86_INS_CMOVNO:
            tritonId = triton::arch::x86::ID_INS_CMOVNO;
            break;

          case triton::extlibs::capstone::X86_INS_CMOVNP:
            tritonId = triton::arch::x86::ID_INS_CMOVNP;
            break;

          case triton::extlibs::capstone::X86_INS_FCMOVNU:
            tritonId = triton::arch::x86::ID_INS_FCMOVNU;
            break;

          case triton::extlibs::capstone::X86_INS_CMOVNS:
            tritonId = triton::arch::x86::ID_INS_CMOVNS;
            break;

          case triton::extlibs::capstone::X86_INS_CMOVO:
            tritonId = triton::arch::x86::ID_INS_CMOVO;
            break;

          case triton::extlibs::capstone::X86_INS_CMOVP:
            tritonId = triton::arch::x86::ID_INS_CMOVP;
            break;

          case triton::extlibs::capstone::X86_INS_FCMOVU:
            tritonId = triton::arch::x86::ID_INS_FCMOVU;
            break;

          case triton::extlibs::capstone::X86_INS_CMOVS:
            tritonId = triton::arch::x86::ID_INS_CMOVS;
            break;

          case triton::extlibs::capstone::X86_INS_CMP:
            tritonId = triton::arch::x86::ID_INS_CMP;
            break;

          case triton::extlibs::capstone::X86_INS_CMPPD:
            tritonId = triton::arch::x86::ID_INS_CMPPD;
            break;

          case triton::extlibs::capstone::X86_INS_CMPPS:
            tritonId = triton::arch::x86::ID_INS_CMPPS;
            break;

          case triton::extlibs::capstone::X86_INS_CMPSB:
            tritonId = triton::arch::x86::ID_INS_CMPSB;
            break;

          case triton::extlibs::capstone::X86_INS_CMPSD:
            tritonId = triton::arch::x86::ID_INS_CMPSD;
            break;

          case triton::extlibs::capstone::X86_INS_CMPSQ:
            tritonId = triton::arch::x86::ID_INS_CMPSQ;
            break;

          case triton::extlibs::capstone::X86_INS_CMPSS:
            tritonId = triton::arch::x86::ID_INS_CMPSS;
            break;

          case triton::extlibs::capstone::X86_INS_CMPSW:
            tritonId = triton::arch::x86::ID_INS_CMPSW;
            break;

          case triton::extlibs::capstone::X86_INS_CMPXCHG16B:
            tritonId = triton::arch::x86::ID_INS_CMPXCHG16B;
            break;

          case triton::extlibs::capstone::X86_INS_CMPXCHG:
            tritonId = triton::arch::x86::ID_INS_CMPXCHG;
            break;

          case triton::extlibs::capstone::X86_INS_CMPXCHG8B:
            tritonId = triton::arch::x86::ID_INS_CMPXCHG8B;
            break;

          case triton::extlibs::capstone::X86_INS_COMISD:
            tritonId = triton::arch::x86::ID_INS_COMISD;
            break;

          case triton::extlibs::capstone::X86_INS_COMISS:
            tritonId = triton::arch::x86::ID_INS_COMISS;
            break;

          case triton::extlibs::capstone::X86_INS_FCOMP:
            tritonId = triton::arch::x86::ID_INS_FCOMP;
            break;

          case triton::extlibs::capstone::X86_INS_FCOMPI:
            tritonId = triton::arch::x86::ID_INS_FCOMPI;
            break;

          case triton::extlibs::capstone::X86_INS_FCOMI:
            tritonId = triton::arch::x86::ID_INS_FCOMI;
            break;

          case triton::extlibs::capstone::X86_INS_FCOM:
            tritonId = triton::arch::x86::ID_INS_FCOM;
            break;

          case triton::extlibs::capstone::X86_INS_FCOS:
            tritonId = triton::arch::x86::ID_INS_FCOS;
            break;

          case triton::extlibs::capstone::X86_INS_CPUID:
            tritonId = triton::arch::x86::ID_INS_CPUID;
            break;

          case triton::extlibs::capstone::X86_INS_CQO:
            tritonId = triton::arch::x86::ID_INS_CQO;
            break;

          case triton::extlibs::capstone::X86_INS_CRC32:
            tritonId = triton::arch::x86::ID_INS_CRC32;
            break;

          case triton::extlibs::capstone::X86_INS_CVTDQ2PD:
            tritonId = triton::arch::x86::ID_INS_CVTDQ2PD;
            break;

          case triton::extlibs::capstone::X86_INS_CVTDQ2PS:
            tritonId = triton::arch::x86::ID_INS_CVTDQ2PS;
            break;

          case triton::extlibs::capstone::X86_INS_CVTPD2DQ:
            tritonId = triton::arch::x86::ID_INS_CVTPD2DQ;
            break;

          case triton::extlibs::capstone::X86_INS_CVTPD2PS:
            tritonId = triton::arch::x86::ID_INS_CVTPD2PS;
            break;

          case triton::extlibs::capstone::X86_INS_CVTPS2DQ:
            tritonId = triton::arch::x86::ID_INS_CVTPS2DQ;
            break;

          case triton::extlibs::capstone::X86_INS_CVTPS2PD:
            tritonId = triton::arch::x86::ID_INS_CVTPS2PD;
            break;

          case triton::extlibs::capstone::X86_INS_CVTSD2SI:
            tritonId = triton::arch::x86::ID_INS_CVTSD2SI;
            break;

          case triton::extlibs::capstone::X86_INS_CVTSD2SS:
            tritonId = triton::arch::x86::ID_INS_CVTSD2SS;
            break;

          case triton::extlibs::capstone::X86_INS_CVTSI2SD:
            tritonId = triton::arch::x86::ID_INS_CVTSI2SD;
            break;

          case triton::extlibs::capstone::X86_INS_CVTSI2SS:
            tritonId = triton::arch::x86::ID_INS_CVTSI2SS;
            break;

          case triton::extlibs::capstone::X86_INS_CVTSS2SD:
            tritonId = triton::arch::x86::ID_INS_CVTSS2SD;
            break;

          case triton::extlibs::capstone::X86_INS_CVTSS2SI:
            tritonId = triton::arch::x86::ID_INS_CVTSS2SI;
            break;

          case triton::extlibs::capstone::X86_INS_CVTTPD2DQ:
            tritonId = triton::arch::x86::ID_INS_CVTTPD2DQ;
            break;

          case triton::extlibs::capstone::X86_INS_CVTTPS2DQ:
            tritonId = triton::arch::x86::ID_INS_CVTTPS2DQ;
            break;

          case triton::extlibs::capstone::X86_INS_CVTTSD2SI:
            tritonId = triton::arch::x86::ID_INS_CVTTSD2SI;
            break;

          case triton::extlibs::capstone::X86_INS_CVTTSS2SI:
            tritonId = triton::arch::x86::ID_INS_CVTTSS2SI;
            break;

          case triton::extlibs::capstone::X86_INS_CWD:
            tritonId = triton::arch::x86::ID_INS_CWD;
            break;

          case triton::extlibs::capstone::X86_INS_CWDE:
            tritonId = triton::arch::x86::ID_INS_CWDE;
            break;

          case triton::extlibs::capstone::X86_INS_DAA:
            tritonId = triton::arch::x86::ID_INS_DAA;
            break;

          case triton::extlibs::capstone::X86_INS_DAS:
            tritonId = triton::arch::x86::ID_INS_DAS;
            break;

          case triton::extlibs::capstone::X86_INS_DATA16:
            tritonId = triton::arch::x86::ID_INS_DATA16;
            break;

          case triton::extlibs::capstone::X86_INS_DEC:
            tritonId = triton::arch::x86::ID_INS_DEC;
            break;

          case triton::extlibs::capstone::X86_INS_DIV:
            tritonId = triton::arch::x86::ID_INS_DIV;
            break;

          case triton::extlibs::capstone::X86_INS_DIVPD:
            tritonId = triton::arch::x86::ID_INS_DIVPD;
            break;

          case triton::extlibs::capstone::X86_INS_DIVPS:
            tritonId = triton::arch::x86::ID_INS_DIVPS;
            break;

          case triton::extlibs::capstone::X86_INS_FDIVR:
            tritonId = triton::arch::x86::ID_INS_FDIVR;
            break;

          case triton::extlibs::capstone::X86_INS_FIDIVR:
            tritonId = triton::arch::x86::ID_INS_FIDIVR;
            break;

          case triton::extlibs::capstone::X86_INS_FDIVRP:
            tritonId = triton::arch::x86::ID_INS_FDIVRP;
            break;

          case triton::extlibs::capstone::X86_INS_DIVSD:
            tritonId = triton::arch::x86::ID_INS_DIVSD;
            break;

          case triton::extlibs::capstone::X86_INS_DIVSS:
            tritonId = triton::arch::x86::ID_INS_DIVSS;
            break;

          case triton::extlibs::capstone::X86_INS_FDIV:
            tritonId = triton::arch::x86::ID_INS_FDIV;
            break;

          case triton::extlibs::capstone::X86_INS_FIDIV:
            tritonId = triton::arch::x86::ID_INS_FIDIV;
            break;

          case triton::extlibs::capstone::X86_INS_FDIVP:
            tritonId = triton::arch::x86::ID_INS_FDIVP;
            break;

          case triton::extlibs::capstone::X86_INS_DPPD:
            tritonId = triton::arch::x86::ID_INS_DPPD;
            break;

          case triton::extlibs::capstone::X86_INS_DPPS:
            tritonId = triton::arch::x86::ID_INS_DPPS;
            break;

          case triton::extlibs::capstone::X86_INS_RET:
            tritonId = triton::arch::x86::ID_INS_RET;
            break;

          case triton::extlibs::capstone::X86_INS_ENCLS:
            tritonId = triton::arch::x86::ID_INS_ENCLS;
            break;

          case triton::extlibs::capstone::X86_INS_ENCLU:
            tritonId = triton::arch::x86::ID_INS_ENCLU;
            break;

          case triton::extlibs::capstone::X86_INS_ENTER:
            tritonId = triton::arch::x86::ID_INS_ENTER;
            break;

          case triton::extlibs::capstone::X86_INS_EXTRACTPS:
            tritonId = triton::arch::x86::ID_INS_EXTRACTPS;
            break;

          case triton::extlibs::capstone::X86_INS_EXTRQ:
            tritonId = triton::arch::x86::ID_INS_EXTRQ;
            break;

          case triton::extlibs::capstone::X86_INS_F2XM1:
            tritonId = triton::arch::x86::ID_INS_F2XM1;
            break;

          case triton::extlibs::capstone::X86_INS_LCALL:
            tritonId = triton::arch::x86::ID_INS_LCALL;
            break;

          case triton::extlibs::capstone::X86_INS_LJMP:
            tritonId = triton::arch::x86::ID_INS_LJMP;
            break;

          case triton::extlibs::capstone::X86_INS_FBLD:
            tritonId = triton::arch::x86::ID_INS_FBLD;
            break;

          case triton::extlibs::capstone::X86_INS_FBSTP:
            tritonId = triton::arch::x86::ID_INS_FBSTP;
            break;

          case triton::extlibs::capstone::X86_INS_FCOMPP:
            tritonId = triton::arch::x86::ID_INS_FCOMPP;
            break;

          case triton::extlibs::capstone::X86_INS_FDECSTP:
            tritonId = triton::arch::x86::ID_INS_FDECSTP;
            break;

          case triton::extlibs::capstone::X86_INS_FEMMS:
            tritonId = triton::arch::x86::ID_INS_FEMMS;
            break;

          case triton::extlibs::capstone::X86_INS_FFREE:
            tritonId = triton::arch::x86::ID_INS_FFREE;
            break;

          case triton::extlibs::capstone::X86_INS_FICOM:
            tritonId = triton::arch::x86::ID_INS_FICOM;
            break;

          case triton::extlibs::capstone::X86_INS_FICOMP:
            tritonId = triton::arch::x86::ID_INS_FICOMP;
            break;

          case triton::extlibs::capstone::X86_INS_FINCSTP:
            tritonId = triton::arch::x86::ID_INS_FINCSTP;
            break;

          case triton::extlibs::capstone::X86_INS_FLDCW:
            tritonId = triton::arch::x86::ID_INS_FLDCW;
            break;

          case triton::extlibs::capstone::X86_INS_FLDENV:
            tritonId = triton::arch::x86::ID_INS_FLDENV;
            break;

          case triton::extlibs::capstone::X86_INS_FLDL2E:
            tritonId = triton::arch::x86::ID_INS_FLDL2E;
            break;

          case triton::extlibs::capstone::X86_INS_FLDL2T:
            tritonId = triton::arch::x86::ID_INS_FLDL2T;
            break;

          case triton::extlibs::capstone::X86_INS_FLDLG2:
            tritonId = triton::arch::x86::ID_INS_FLDLG2;
            break;

          case triton::extlibs::capstone::X86_INS_FLDLN2:
            tritonId = triton::arch::x86::ID_INS_FLDLN2;
            break;

          case triton::extlibs::capstone::X86_INS_FLDPI:
            tritonId = triton::arch::x86::ID_INS_FLDPI;
            break;

          case triton::extlibs::capstone::X86_INS_FNCLEX:
            tritonId = triton::arch::x86::ID_INS_FNCLEX;
            break;

          case triton::extlibs::capstone::X86_INS_FNINIT:
            tritonId = triton::arch::x86::ID_INS_FNINIT;
            break;

          case triton::extlibs::capstone::X86_INS_FNOP:
            tritonId = triton::arch::x86::ID_INS_FNOP;
            break;

          case triton::extlibs::capstone::X86_INS_FNSTCW:
            tritonId = triton::arch::x86::ID_INS_FNSTCW;
            break;

          case triton::extlibs::capstone::X86_INS_FNSTSW:
            tritonId = triton::arch::x86::ID_INS_FNSTSW;
            break;

          case triton::extlibs::capstone::X86_INS_FPATAN:
            tritonId = triton::arch::x86::ID_INS_FPATAN;
            break;

          case triton::extlibs::capstone::X86_INS_FPREM:
            tritonId = triton::arch::x86::ID_INS_FPREM;
            break;

          case triton::extlibs::capstone::X86_INS_FPREM1:
            tritonId = triton::arch::x86::ID_INS_FPREM1;
            break;

          case triton::extlibs::capstone::X86_INS_FPTAN:
            tritonId = triton::arch::x86::ID_INS_FPTAN;
            break;

          case triton::extlibs::capstone::X86_INS_FRNDINT:
            tritonId = triton::arch::x86::ID_INS_FRNDINT;
            break;

          case triton::extlibs::capstone::X86_INS_FRSTOR:
            tritonId = triton::arch::x86::ID_INS_FRSTOR;
            break;

          case triton::extlibs::capstone::X86_INS_FNSAVE:
            tritonId = triton::arch::x86::ID_INS_FNSAVE;
            break;

          case triton::extlibs::capstone::X86_INS_FSCALE:
            tritonId = triton::arch::x86::ID_INS_FSCALE;
            break;

          case triton::extlibs::capstone::X86_INS_FSETPM:
            tritonId = triton::arch::x86::ID_INS_FSETPM;
            break;

          case triton::extlibs::capstone::X86_INS_FSINCOS:
            tritonId = triton::arch::x86::ID_INS_FSINCOS;
            break;

          case triton::extlibs::capstone::X86_INS_FNSTENV:
            tritonId = triton::arch::x86::ID_INS_FNSTENV;
            break;

          case triton::extlibs::capstone::X86_INS_FXAM:
            tritonId = triton::arch::x86::ID_INS_FXAM;
            break;

          case triton::extlibs::capstone::X86_INS_FXRSTOR:
            tritonId = triton::arch::x86::ID_INS_FXRSTOR;
            break;

          case triton::extlibs::capstone::X86_INS_FXRSTOR64:
            tritonId = triton::arch::x86::ID_INS_FXRSTOR64;
            break;

          case triton::extlibs::capstone::X86_INS_FXSAVE:
            tritonId = triton::arch::x86::ID_INS_FXSAVE;
            break;

          case triton::extlibs::capstone::X86_INS_FXSAVE64:
            tritonId = triton::arch::x86::ID_INS_FXSAVE64;
            break;

          case triton::extlibs::capstone::X86_INS_FXTRACT:
            tritonId = triton::arch::x86::ID_INS_FXTRACT;
            break;

          case triton::extlibs::capstone::X86_INS_FYL2X:
            tritonId = triton::arch::x86::ID_INS_FYL2X;
            break;

          case triton::extlibs::capstone::X86_INS_FYL2XP1:
            tritonId = triton::arch::x86::ID_INS_FYL2XP1;
            break;

          case triton::extlibs::capstone::X86_INS_MOVAPD:
            tritonId = triton::arch::x86::ID_INS_MOVAPD;
            break;

          case triton::extlibs::capstone::X86_INS_MOVAPS:
            tritonId = triton::arch::x86::ID_INS_MOVAPS;
            break;

          case triton::extlibs::capstone::X86_INS_ORPD:
            tritonId = triton::arch::x86::ID_INS_ORPD;
            break;

          case triton::extlibs::capstone::X86_INS_ORPS:
            tritonId = triton::arch::x86::ID_INS_ORPS;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVAPD:
            tritonId = triton::arch::x86::ID_INS_VMOVAPD;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVAPS:
            tritonId = triton::arch::x86::ID_INS_VMOVAPS;
            break;

          case triton::extlibs::capstone::X86_INS_XORPD:
            tritonId = triton::arch::x86::ID_INS_XORPD;
            break;

          case triton::extlibs::capstone::X86_INS_XORPS:
            tritonId = triton::arch::x86::ID_INS_XORPS;
            break;

          case triton::extlibs::capstone::X86_INS_GETSEC:
            tritonId = triton::arch::x86::ID_INS_GETSEC;
            break;

          case triton::extlibs::capstone::X86_INS_HADDPD:
            tritonId = triton::arch::x86::ID_INS_HADDPD;
            break;

          case triton::extlibs::capstone::X86_INS_HADDPS:
            tritonId = triton::arch::x86::ID_INS_HADDPS;
            break;

          case triton::extlibs::capstone::X86_INS_HLT:
            tritonId = triton::arch::x86::ID_INS_HLT;
            break;

          case triton::extlibs::capstone::X86_INS_HSUBPD:
            tritonId = triton::arch::x86::ID_INS_HSUBPD;
            break;

          case triton::extlibs::capstone::X86_INS_HSUBPS:
            tritonId = triton::arch::x86::ID_INS_HSUBPS;
            break;

          case triton::extlibs::capstone::X86_INS_IDIV:
            tritonId = triton::arch::x86::ID_INS_IDIV;
            break;

          case triton::extlibs::capstone::X86_INS_FILD:
            tritonId = triton::arch::x86::ID_INS_FILD;
            break;

          case triton::extlibs::capstone::X86_INS_IMUL:
            tritonId = triton::arch::x86::ID_INS_IMUL;
            break;

          case triton::extlibs::capstone::X86_INS_IN:
            tritonId = triton::arch::x86::ID_INS_IN;
            break;

          case triton::extlibs::capstone::X86_INS_INC:
            tritonId = triton::arch::x86::ID_INS_INC;
            break;

          case triton::extlibs::capstone::X86_INS_INSB:
            tritonId = triton::arch::x86::ID_INS_INSB;
            break;

          case triton::extlibs::capstone::X86_INS_INSERTPS:
            tritonId = triton::arch::x86::ID_INS_INSERTPS;
            break;

          case triton::extlibs::capstone::X86_INS_INSERTQ:
            tritonId = triton::arch::x86::ID_INS_INSERTQ;
            break;

          case triton::extlibs::capstone::X86_INS_INSD:
            tritonId = triton::arch::x86::ID_INS_INSD;
            break;

          case triton::extlibs::capstone::X86_INS_INSW:
            tritonId = triton::arch::x86::ID_INS_INSW;
            break;

          case triton::extlibs::capstone::X86_INS_INT:
            tritonId = triton::arch::x86::ID_INS_INT;
            break;

          case triton::extlibs::capstone::X86_INS_INT1:
            tritonId = triton::arch::x86::ID_INS_INT1;
            break;

          case triton::extlibs::capstone::X86_INS_INT3:
            tritonId = triton::arch::x86::ID_INS_INT3;
            break;

          case triton::extlibs::capstone::X86_INS_INTO:
            tritonId = triton::arch::x86::ID_INS_INTO;
            break;

          case triton::extlibs::capstone::X86_INS_INVD:
            tritonId = triton::arch::x86::ID_INS_INVD;
            break;

          case triton::extlibs::capstone::X86_INS_INVEPT:
            tritonId = triton::arch::x86::ID_INS_INVEPT;
            break;

          case triton::extlibs::capstone::X86_INS_INVLPG:
            tritonId = triton::arch::x86::ID_INS_INVLPG;
            break;

          case triton::extlibs::capstone::X86_INS_INVLPGA:
            tritonId = triton::arch::x86::ID_INS_INVLPGA;
            break;

          case triton::extlibs::capstone::X86_INS_INVPCID:
            tritonId = triton::arch::x86::ID_INS_INVPCID;
            break;

          case triton::extlibs::capstone::X86_INS_INVVPID:
            tritonId = triton::arch::x86::ID_INS_INVVPID;
            break;

          case triton::extlibs::capstone::X86_INS_IRET:
            tritonId = triton::arch::x86::ID_INS_IRET;
            break;

          case triton::extlibs::capstone::X86_INS_IRETD:
            tritonId = triton::arch::x86::ID_INS_IRETD;
            break;

          case triton::extlibs::capstone::X86_INS_IRETQ:
            tritonId = triton::arch::x86::ID_INS_IRETQ;
            break;

          case triton::extlibs::capstone::X86_INS_FISTTP:
            tritonId = triton::arch::x86::ID_INS_FISTTP;
            break;

          case triton::extlibs::capstone::X86_INS_FIST:
            tritonId = triton::arch::x86::ID_INS_FIST;
            break;

          case triton::extlibs::capstone::X86_INS_FISTP:
            tritonId = triton::arch::x86::ID_INS_FISTP;
            break;

          case triton::extlibs::capstone::X86_INS_UCOMISD:
            tritonId = triton::arch::x86::ID_INS_UCOMISD;
            break;

          case triton::extlibs::capstone::X86_INS_UCOMISS:
            tritonId = triton::arch::x86::ID_INS_UCOMISS;
            break;

          case triton::extlibs::capstone::X86_INS_VCMP:
            tritonId = triton::arch::x86::ID_INS_VCMP;
            break;

          case triton::extlibs::capstone::X86_INS_VCOMISD:
            tritonId = triton::arch::x86::ID_INS_VCOMISD;
            break;

          case triton::extlibs::capstone::X86_INS_VCOMISS:
            tritonId = triton::arch::x86::ID_INS_VCOMISS;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTSD2SS:
            tritonId = triton::arch::x86::ID_INS_VCVTSD2SS;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTSI2SD:
            tritonId = triton::arch::x86::ID_INS_VCVTSI2SD;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTSI2SS:
            tritonId = triton::arch::x86::ID_INS_VCVTSI2SS;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTSS2SD:
            tritonId = triton::arch::x86::ID_INS_VCVTSS2SD;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTTSD2SI:
            tritonId = triton::arch::x86::ID_INS_VCVTTSD2SI;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTTSD2USI:
            tritonId = triton::arch::x86::ID_INS_VCVTTSD2USI;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTTSS2SI:
            tritonId = triton::arch::x86::ID_INS_VCVTTSS2SI;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTTSS2USI:
            tritonId = triton::arch::x86::ID_INS_VCVTTSS2USI;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTUSI2SD:
            tritonId = triton::arch::x86::ID_INS_VCVTUSI2SD;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTUSI2SS:
            tritonId = triton::arch::x86::ID_INS_VCVTUSI2SS;
            break;

          case triton::extlibs::capstone::X86_INS_VUCOMISD:
            tritonId = triton::arch::x86::ID_INS_VUCOMISD;
            break;

          case triton::extlibs::capstone::X86_INS_VUCOMISS:
            tritonId = triton::arch::x86::ID_INS_VUCOMISS;
            break;

          case triton::extlibs::capstone::X86_INS_JAE:
            tritonId = triton::arch::x86::ID_INS_JAE;
            break;

          case triton::extlibs::capstone::X86_INS_JA:
            tritonId = triton::arch::x86::ID_INS_JA;
            break;

          case triton::extlibs::capstone::X86_INS_JBE:
            tritonId = triton::arch::x86::ID_INS_JBE;
            break;

          case triton::extlibs::capstone::X86_INS_JB:
            tritonId = triton::arch::x86::ID_INS_JB;
            break;

          case triton::extlibs::capstone::X86_INS_JCXZ:
            tritonId = triton::arch::x86::ID_INS_JCXZ;
            break;

          case triton::extlibs::capstone::X86_INS_JECXZ:
            tritonId = triton::arch::x86::ID_INS_JECXZ;
            break;

          case triton::extlibs::capstone::X86_INS_JE:
            tritonId = triton::arch::x86::ID_INS_JE;
            break;

          case triton::extlibs::capstone::X86_INS_JGE:
            tritonId = triton::arch::x86::ID_INS_JGE;
            break;

          case triton::extlibs::capstone::X86_INS_JG:
            tritonId = triton::arch::x86::ID_INS_JG;
            break;

          case triton::extlibs::capstone::X86_INS_JLE:
            tritonId = triton::arch::x86::ID_INS_JLE;
            break;

          case triton::extlibs::capstone::X86_INS_JL:
            tritonId = triton::arch::x86::ID_INS_JL;
            break;

          case triton::extlibs::capstone::X86_INS_JMP:
            tritonId = triton::arch::x86::ID_INS_JMP;
            break;

          case triton::extlibs::capstone::X86_INS_JNE:
            tritonId = triton::arch::x86::ID_INS_JNE;
            break;

          case triton::extlibs::capstone::X86_INS_JNO:
            tritonId = triton::arch::x86::ID_INS_JNO;
            break;

          case triton::extlibs::capstone::X86_INS_JNP:
            tritonId = triton::arch::x86::ID_INS_JNP;
            break;

          case triton::extlibs::capstone::X86_INS_JNS:
            tritonId = triton::arch::x86::ID_INS_JNS;
            break;

          case triton::extlibs::capstone::X86_INS_JO:
            tritonId = triton::arch::x86::ID_INS_JO;
            break;

          case triton::extlibs::capstone::X86_INS_JP:
            tritonId = triton::arch::x86::ID_INS_JP;
            break;

          case triton::extlibs::capstone::X86_INS_JRCXZ:
            tritonId = triton::arch::x86::ID_INS_JRCXZ;
            break;

          case triton::extlibs::capstone::X86_INS_JS:
            tritonId = triton::arch::x86::ID_INS_JS;
            break;

          case triton::extlibs::capstone::X86_INS_KANDB:
            tritonId = triton::arch::x86::ID_INS_KANDB;
            break;

          case triton::extlibs::capstone::X86_INS_KANDD:
            tritonId = triton::arch::x86::ID_INS_KANDD;
            break;

          case triton::extlibs::capstone::X86_INS_KANDNB:
            tritonId = triton::arch::x86::ID_INS_KANDNB;
            break;

          case triton::extlibs::capstone::X86_INS_KANDND:
            tritonId = triton::arch::x86::ID_INS_KANDND;
            break;

          case triton::extlibs::capstone::X86_INS_KANDNQ:
            tritonId = triton::arch::x86::ID_INS_KANDNQ;
            break;

          case triton::extlibs::capstone::X86_INS_KANDNW:
            tritonId = triton::arch::x86::ID_INS_KANDNW;
            break;

          case triton::extlibs::capstone::X86_INS_KANDQ:
            tritonId = triton::arch::x86::ID_INS_KANDQ;
            break;

          case triton::extlibs::capstone::X86_INS_KANDW:
            tritonId = triton::arch::x86::ID_INS_KANDW;
            break;

          case triton::extlibs::capstone::X86_INS_KMOVB:
            tritonId = triton::arch::x86::ID_INS_KMOVB;
            break;

          case triton::extlibs::capstone::X86_INS_KMOVD:
            tritonId = triton::arch::x86::ID_INS_KMOVD;
            break;

          case triton::extlibs::capstone::X86_INS_KMOVQ:
            tritonId = triton::arch::x86::ID_INS_KMOVQ;
            break;

          case triton::extlibs::capstone::X86_INS_KMOVW:
            tritonId = triton::arch::x86::ID_INS_KMOVW;
            break;

          case triton::extlibs::capstone::X86_INS_KNOTB:
            tritonId = triton::arch::x86::ID_INS_KNOTB;
            break;

          case triton::extlibs::capstone::X86_INS_KNOTD:
            tritonId = triton::arch::x86::ID_INS_KNOTD;
            break;

          case triton::extlibs::capstone::X86_INS_KNOTQ:
            tritonId = triton::arch::x86::ID_INS_KNOTQ;
            break;

          case triton::extlibs::capstone::X86_INS_KNOTW:
            tritonId = triton::arch::x86::ID_INS_KNOTW;
            break;

          case triton::extlibs::capstone::X86_INS_KORB:
            tritonId = triton::arch::x86::ID_INS_KORB;
            break;

          case triton::extlibs::capstone::X86_INS_KORD:
            tritonId = triton::arch::x86::ID_INS_KORD;
            break;

          case triton::extlibs::capstone::X86_INS_KORQ:
            tritonId = triton::arch::x86::ID_INS_KORQ;
            break;

          case triton::extlibs::capstone::X86_INS_KORTESTW:
            tritonId = triton::arch::x86::ID_INS_KORTESTW;
            break;

          case triton::extlibs::capstone::X86_INS_KORW:
            tritonId = triton::arch::x86::ID_INS_KORW;
            break;

          case triton::extlibs::capstone::X86_INS_KSHIFTLW:
            tritonId = triton::arch::x86::ID_INS_KSHIFTLW;
            break;

          case triton::extlibs::capstone::X86_INS_KSHIFTRW:
            tritonId = triton::arch::x86::ID_INS_KSHIFTRW;
            break;

          case triton::extlibs::capstone::X86_INS_KUNPCKBW:
            tritonId = triton::arch::x86::ID_INS_KUNPCKBW;
            break;

          case triton::extlibs::capstone::X86_INS_KXNORB:
            tritonId = triton::arch::x86::ID_INS_KXNORB;
            break;

          case triton::extlibs::capstone::X86_INS_KXNORD:
            tritonId = triton::arch::x86::ID_INS_KXNORD;
            break;

          case triton::extlibs::capstone::X86_INS_KXNORQ:
            tritonId = triton::arch::x86::ID_INS_KXNORQ;
            break;

          case triton::extlibs::capstone::X86_INS_KXNORW:
            tritonId = triton::arch::x86::ID_INS_KXNORW;
            break;

          case triton::extlibs::capstone::X86_INS_KXORB:
            tritonId = triton::arch::x86::ID_INS_KXORB;
            break;

          case triton::extlibs::capstone::X86_INS_KXORD:
            tritonId = triton::arch::x86::ID_INS_KXORD;
            break;

          case triton::extlibs::capstone::X86_INS_KXORQ:
            tritonId = triton::arch::x86::ID_INS_KXORQ;
            break;

          case triton::extlibs::capstone::X86_INS_KXORW:
            tritonId = triton::arch::x86::ID_INS_KXORW;
            break;

          case triton::extlibs::capstone::X86_INS_LAHF:
            tritonId = triton::arch::x86::ID_INS_LAHF;
            break;

          case triton::extlibs::capstone::X86_INS_LAR:
            tritonId = triton::arch::x86::ID_INS_LAR;
            break;

          case triton::extlibs::capstone::X86_INS_LDDQU:
            tritonId = triton::arch::x86::ID_INS_LDDQU;
            break;

          case triton::extlibs::capstone::X86_INS_LDMXCSR:
            tritonId = triton::arch::x86::ID_INS_LDMXCSR;
            break;

          case triton::extlibs::capstone::X86_INS_LDS:
            tritonId = triton::arch::x86::ID_INS_LDS;
            break;

          case triton::extlibs::capstone::X86_INS_FLDZ:
            tritonId = triton::arch::x86::ID_INS_FLDZ;
            break;

          case triton::extlibs::capstone::X86_INS_FLD1:
            tritonId = triton::arch::x86::ID_INS_FLD1;
            break;

          case triton::extlibs::capstone::X86_INS_FLD:
            tritonId = triton::arch::x86::ID_INS_FLD;
            break;

          case triton::extlibs::capstone::X86_INS_LEA:
            tritonId = triton::arch::x86::ID_INS_LEA;
            break;

          case triton::extlibs::capstone::X86_INS_LEAVE:
            tritonId = triton::arch::x86::ID_INS_LEAVE;
            break;

          case triton::extlibs::capstone::X86_INS_LES:
            tritonId = triton::arch::x86::ID_INS_LES;
            break;

          case triton::extlibs::capstone::X86_INS_LFENCE:
            tritonId = triton::arch::x86::ID_INS_LFENCE;
            break;

          case triton::extlibs::capstone::X86_INS_LFS:
            tritonId = triton::arch::x86::ID_INS_LFS;
            break;

          case triton::extlibs::capstone::X86_INS_LGDT:
            tritonId = triton::arch::x86::ID_INS_LGDT;
            break;

          case triton::extlibs::capstone::X86_INS_LGS:
            tritonId = triton::arch::x86::ID_INS_LGS;
            break;

          case triton::extlibs::capstone::X86_INS_LIDT:
            tritonId = triton::arch::x86::ID_INS_LIDT;
            break;

          case triton::extlibs::capstone::X86_INS_LLDT:
            tritonId = triton::arch::x86::ID_INS_LLDT;
            break;

          case triton::extlibs::capstone::X86_INS_LMSW:
            tritonId = triton::arch::x86::ID_INS_LMSW;
            break;

          case triton::extlibs::capstone::X86_INS_OR:
            tritonId = triton::arch::x86::ID_INS_OR;
            break;

          case triton::extlibs::capstone::X86_INS_SUB:
            tritonId = triton::arch::x86::ID_INS_SUB;
            break;

          case triton::extlibs::capstone::X86_INS_XOR:
            tritonId = triton::arch::x86::ID_INS_XOR;
            break;

          case triton::extlibs::capstone::X86_INS_LODSB:
            tritonId = triton::arch::x86::ID_INS_LODSB;
            break;

          case triton::extlibs::capstone::X86_INS_LODSD:
            tritonId = triton::arch::x86::ID_INS_LODSD;
            break;

          case triton::extlibs::capstone::X86_INS_LODSQ:
            tritonId = triton::arch::x86::ID_INS_LODSQ;
            break;

          case triton::extlibs::capstone::X86_INS_LODSW:
            tritonId = triton::arch::x86::ID_INS_LODSW;
            break;

          case triton::extlibs::capstone::X86_INS_LOOP:
            tritonId = triton::arch::x86::ID_INS_LOOP;
            break;

          case triton::extlibs::capstone::X86_INS_LOOPE:
            tritonId = triton::arch::x86::ID_INS_LOOPE;
            break;

          case triton::extlibs::capstone::X86_INS_LOOPNE:
            tritonId = triton::arch::x86::ID_INS_LOOPNE;
            break;

          case triton::extlibs::capstone::X86_INS_RETF:
            tritonId = triton::arch::x86::ID_INS_RETF;
            break;

          case triton::extlibs::capstone::X86_INS_RETFQ:
            tritonId = triton::arch::x86::ID_INS_RETFQ;
            break;

          case triton::extlibs::capstone::X86_INS_LSL:
            tritonId = triton::arch::x86::ID_INS_LSL;
            break;

          case triton::extlibs::capstone::X86_INS_LSS:
            tritonId = triton::arch::x86::ID_INS_LSS;
            break;

          case triton::extlibs::capstone::X86_INS_LTR:
            tritonId = triton::arch::x86::ID_INS_LTR;
            break;

          case triton::extlibs::capstone::X86_INS_XADD:
            tritonId = triton::arch::x86::ID_INS_XADD;
            break;

          case triton::extlibs::capstone::X86_INS_LZCNT:
            tritonId = triton::arch::x86::ID_INS_LZCNT;
            break;

          case triton::extlibs::capstone::X86_INS_MASKMOVDQU:
            tritonId = triton::arch::x86::ID_INS_MASKMOVDQU;
            break;

          case triton::extlibs::capstone::X86_INS_MAXPD:
            tritonId = triton::arch::x86::ID_INS_MAXPD;
            break;

          case triton::extlibs::capstone::X86_INS_MAXPS:
            tritonId = triton::arch::x86::ID_INS_MAXPS;
            break;

          case triton::extlibs::capstone::X86_INS_MAXSD:
            tritonId = triton::arch::x86::ID_INS_MAXSD;
            break;

          case triton::extlibs::capstone::X86_INS_MAXSS:
            tritonId = triton::arch::x86::ID_INS_MAXSS;
            break;

          case triton::extlibs::capstone::X86_INS_MFENCE:
            tritonId = triton::arch::x86::ID_INS_MFENCE;
            break;

          case triton::extlibs::capstone::X86_INS_MINPD:
            tritonId = triton::arch::x86::ID_INS_MINPD;
            break;

          case triton::extlibs::capstone::X86_INS_MINPS:
            tritonId = triton::arch::x86::ID_INS_MINPS;
            break;

          case triton::extlibs::capstone::X86_INS_MINSD:
            tritonId = triton::arch::x86::ID_INS_MINSD;
            break;

          case triton::extlibs::capstone::X86_INS_MINSS:
            tritonId = triton::arch::x86::ID_INS_MINSS;
            break;

          case triton::extlibs::capstone::X86_INS_CVTPD2PI:
            tritonId = triton::arch::x86::ID_INS_CVTPD2PI;
            break;

          case triton::extlibs::capstone::X86_INS_CVTPI2PD:
            tritonId = triton::arch::x86::ID_INS_CVTPI2PD;
            break;

          case triton::extlibs::capstone::X86_INS_CVTPI2PS:
            tritonId = triton::arch::x86::ID_INS_CVTPI2PS;
            break;

          case triton::extlibs::capstone::X86_INS_CVTPS2PI:
            tritonId = triton::arch::x86::ID_INS_CVTPS2PI;
            break;

          case triton::extlibs::capstone::X86_INS_CVTTPD2PI:
            tritonId = triton::arch::x86::ID_INS_CVTTPD2PI;
            break;

          case triton::extlibs::capstone::X86_INS_CVTTPS2PI:
            tritonId = triton::arch::x86::ID_INS_CVTTPS2PI;
            break;

          case triton::extlibs::capstone::X86_INS_EMMS:
            tritonId = triton::arch::x86::ID_INS_EMMS;
            break;

          case triton::extlibs::capstone::X86_INS_MASKMOVQ:
            tritonId = triton::arch::x86::ID_INS_MASKMOVQ;
            break;

          case triton::extlibs::capstone::X86_INS_MOVD:
            tritonId = triton::arch::x86::ID_INS_MOVD;
            break;

          case triton::extlibs::capstone::X86_INS_MOVDQ2Q:
            tritonId = triton::arch::x86::ID_INS_MOVDQ2Q;
            break;

          case triton::extlibs::capstone::X86_INS_MOVNTQ:
            tritonId = triton::arch::x86::ID_INS_MOVNTQ;
            break;

          case triton::extlibs::capstone::X86_INS_MOVQ2DQ:
            tritonId = triton::arch::x86::ID_INS_MOVQ2DQ;
            break;

          case triton::extlibs::capstone::X86_INS_MOVQ:
            tritonId = triton::arch::x86::ID_INS_MOVQ;
            break;

          case triton::extlibs::capstone::X86_INS_PABSB:
            tritonId = triton::arch::x86::ID_INS_PABSB;
            break;

          case triton::extlibs::capstone::X86_INS_PABSD:
            tritonId = triton::arch::x86::ID_INS_PABSD;
            break;

          case triton::extlibs::capstone::X86_INS_PABSW:
            tritonId = triton::arch::x86::ID_INS_PABSW;
            break;

          case triton::extlibs::capstone::X86_INS_PACKSSDW:
            tritonId = triton::arch::x86::ID_INS_PACKSSDW;
            break;

          case triton::extlibs::capstone::X86_INS_PACKSSWB:
            tritonId = triton::arch::x86::ID_INS_PACKSSWB;
            break;

          case triton::extlibs::capstone::X86_INS_PACKUSWB:
            tritonId = triton::arch::x86::ID_INS_PACKUSWB;
            break;

          case triton::extlibs::capstone::X86_INS_PADDB:
            tritonId = triton::arch::x86::ID_INS_PADDB;
            break;

          case triton::extlibs::capstone::X86_INS_PADDD:
            tritonId = triton::arch::x86::ID_INS_PADDD;
            break;

          case triton::extlibs::capstone::X86_INS_PADDQ:
            tritonId = triton::arch::x86::ID_INS_PADDQ;
            break;

          case triton::extlibs::capstone::X86_INS_PADDSB:
            tritonId = triton::arch::x86::ID_INS_PADDSB;
            break;

          case triton::extlibs::capstone::X86_INS_PADDSW:
            tritonId = triton::arch::x86::ID_INS_PADDSW;
            break;

          case triton::extlibs::capstone::X86_INS_PADDUSB:
            tritonId = triton::arch::x86::ID_INS_PADDUSB;
            break;

          case triton::extlibs::capstone::X86_INS_PADDUSW:
            tritonId = triton::arch::x86::ID_INS_PADDUSW;
            break;

          case triton::extlibs::capstone::X86_INS_PADDW:
            tritonId = triton::arch::x86::ID_INS_PADDW;
            break;

          case triton::extlibs::capstone::X86_INS_PALIGNR:
            tritonId = triton::arch::x86::ID_INS_PALIGNR;
            break;

          case triton::extlibs::capstone::X86_INS_PANDN:
            tritonId = triton::arch::x86::ID_INS_PANDN;
            break;

          case triton::extlibs::capstone::X86_INS_PAND:
            tritonId = triton::arch::x86::ID_INS_PAND;
            break;

          case triton::extlibs::capstone::X86_INS_PAVGB:
            tritonId = triton::arch::x86::ID_INS_PAVGB;
            break;

          case triton::extlibs::capstone::X86_INS_PAVGW:
            tritonId = triton::arch::x86::ID_INS_PAVGW;
            break;

          case triton::extlibs::capstone::X86_INS_PCMPEQB:
            tritonId = triton::arch::x86::ID_INS_PCMPEQB;
            break;

          case triton::extlibs::capstone::X86_INS_PCMPEQD:
            tritonId = triton::arch::x86::ID_INS_PCMPEQD;
            break;

          case triton::extlibs::capstone::X86_INS_PCMPEQW:
            tritonId = triton::arch::x86::ID_INS_PCMPEQW;
            break;

          case triton::extlibs::capstone::X86_INS_PCMPGTB:
            tritonId = triton::arch::x86::ID_INS_PCMPGTB;
            break;

          case triton::extlibs::capstone::X86_INS_PCMPGTD:
            tritonId = triton::arch::x86::ID_INS_PCMPGTD;
            break;

          case triton::extlibs::capstone::X86_INS_PCMPGTW:
            tritonId = triton::arch::x86::ID_INS_PCMPGTW;
            break;

          case triton::extlibs::capstone::X86_INS_PEXTRW:
            tritonId = triton::arch::x86::ID_INS_PEXTRW;
            break;

          case triton::extlibs::capstone::X86_INS_PHADDSW:
            tritonId = triton::arch::x86::ID_INS_PHADDSW;
            break;

          case triton::extlibs::capstone::X86_INS_PHADDW:
            tritonId = triton::arch::x86::ID_INS_PHADDW;
            break;

          case triton::extlibs::capstone::X86_INS_PHADDD:
            tritonId = triton::arch::x86::ID_INS_PHADDD;
            break;

          case triton::extlibs::capstone::X86_INS_PHSUBD:
            tritonId = triton::arch::x86::ID_INS_PHSUBD;
            break;

          case triton::extlibs::capstone::X86_INS_PHSUBSW:
            tritonId = triton::arch::x86::ID_INS_PHSUBSW;
            break;

          case triton::extlibs::capstone::X86_INS_PHSUBW:
            tritonId = triton::arch::x86::ID_INS_PHSUBW;
            break;

          case triton::extlibs::capstone::X86_INS_PINSRW:
            tritonId = triton::arch::x86::ID_INS_PINSRW;
            break;

          case triton::extlibs::capstone::X86_INS_PMADDUBSW:
            tritonId = triton::arch::x86::ID_INS_PMADDUBSW;
            break;

          case triton::extlibs::capstone::X86_INS_PMADDWD:
            tritonId = triton::arch::x86::ID_INS_PMADDWD;
            break;

          case triton::extlibs::capstone::X86_INS_PMAXSW:
            tritonId = triton::arch::x86::ID_INS_PMAXSW;
            break;

          case triton::extlibs::capstone::X86_INS_PMAXUB:
            tritonId = triton::arch::x86::ID_INS_PMAXUB;
            break;

          case triton::extlibs::capstone::X86_INS_PMINSW:
            tritonId = triton::arch::x86::ID_INS_PMINSW;
            break;

          case triton::extlibs::capstone::X86_INS_PMINUB:
            tritonId = triton::arch::x86::ID_INS_PMINUB;
            break;

          case triton::extlibs::capstone::X86_INS_PMOVMSKB:
            tritonId = triton::arch::x86::ID_INS_PMOVMSKB;
            break;

          case triton::extlibs::capstone::X86_INS_PMULHRSW:
            tritonId = triton::arch::x86::ID_INS_PMULHRSW;
            break;

          case triton::extlibs::capstone::X86_INS_PMULHUW:
            tritonId = triton::arch::x86::ID_INS_PMULHUW;
            break;

          case triton::extlibs::capstone::X86_INS_PMULHW:
            tritonId = triton::arch::x86::ID_INS_PMULHW;
            break;

          case triton::extlibs::capstone::X86_INS_PMULLW:
            tritonId = triton::arch::x86::ID_INS_PMULLW;
            break;

          case triton::extlibs::capstone::X86_INS_PMULUDQ:
            tritonId = triton::arch::x86::ID_INS_PMULUDQ;
            break;

          case triton::extlibs::capstone::X86_INS_POR:
            tritonId = triton::arch::x86::ID_INS_POR;
            break;

          case triton::extlibs::capstone::X86_INS_PSADBW:
            tritonId = triton::arch::x86::ID_INS_PSADBW;
            break;

          case triton::extlibs::capstone::X86_INS_PSHUFB:
            tritonId = triton::arch::x86::ID_INS_PSHUFB;
            break;

          case triton::extlibs::capstone::X86_INS_PSHUFW:
            tritonId = triton::arch::x86::ID_INS_PSHUFW;
            break;

          case triton::extlibs::capstone::X86_INS_PSIGNB:
            tritonId = triton::arch::x86::ID_INS_PSIGNB;
            break;

          case triton::extlibs::capstone::X86_INS_PSIGND:
            tritonId = triton::arch::x86::ID_INS_PSIGND;
            break;

          case triton::extlibs::capstone::X86_INS_PSIGNW:
            tritonId = triton::arch::x86::ID_INS_PSIGNW;
            break;

          case triton::extlibs::capstone::X86_INS_PSLLD:
            tritonId = triton::arch::x86::ID_INS_PSLLD;
            break;

          case triton::extlibs::capstone::X86_INS_PSLLQ:
            tritonId = triton::arch::x86::ID_INS_PSLLQ;
            break;

          case triton::extlibs::capstone::X86_INS_PSLLW:
            tritonId = triton::arch::x86::ID_INS_PSLLW;
            break;

          case triton::extlibs::capstone::X86_INS_PSRAD:
            tritonId = triton::arch::x86::ID_INS_PSRAD;
            break;

          case triton::extlibs::capstone::X86_INS_PSRAW:
            tritonId = triton::arch::x86::ID_INS_PSRAW;
            break;

          case triton::extlibs::capstone::X86_INS_PSRLD:
            tritonId = triton::arch::x86::ID_INS_PSRLD;
            break;

          case triton::extlibs::capstone::X86_INS_PSRLQ:
            tritonId = triton::arch::x86::ID_INS_PSRLQ;
            break;

          case triton::extlibs::capstone::X86_INS_PSRLW:
            tritonId = triton::arch::x86::ID_INS_PSRLW;
            break;

          case triton::extlibs::capstone::X86_INS_PSUBB:
            tritonId = triton::arch::x86::ID_INS_PSUBB;
            break;

          case triton::extlibs::capstone::X86_INS_PSUBD:
            tritonId = triton::arch::x86::ID_INS_PSUBD;
            break;

          case triton::extlibs::capstone::X86_INS_PSUBQ:
            tritonId = triton::arch::x86::ID_INS_PSUBQ;
            break;

          case triton::extlibs::capstone::X86_INS_PSUBSB:
            tritonId = triton::arch::x86::ID_INS_PSUBSB;
            break;

          case triton::extlibs::capstone::X86_INS_PSUBSW:
            tritonId = triton::arch::x86::ID_INS_PSUBSW;
            break;

          case triton::extlibs::capstone::X86_INS_PSUBUSB:
            tritonId = triton::arch::x86::ID_INS_PSUBUSB;
            break;

          case triton::extlibs::capstone::X86_INS_PSUBUSW:
            tritonId = triton::arch::x86::ID_INS_PSUBUSW;
            break;

          case triton::extlibs::capstone::X86_INS_PSUBW:
            tritonId = triton::arch::x86::ID_INS_PSUBW;
            break;

          case triton::extlibs::capstone::X86_INS_PUNPCKHBW:
            tritonId = triton::arch::x86::ID_INS_PUNPCKHBW;
            break;

          case triton::extlibs::capstone::X86_INS_PUNPCKHDQ:
            tritonId = triton::arch::x86::ID_INS_PUNPCKHDQ;
            break;

          case triton::extlibs::capstone::X86_INS_PUNPCKHWD:
            tritonId = triton::arch::x86::ID_INS_PUNPCKHWD;
            break;

          case triton::extlibs::capstone::X86_INS_PUNPCKLBW:
            tritonId = triton::arch::x86::ID_INS_PUNPCKLBW;
            break;

          case triton::extlibs::capstone::X86_INS_PUNPCKLDQ:
            tritonId = triton::arch::x86::ID_INS_PUNPCKLDQ;
            break;

          case triton::extlibs::capstone::X86_INS_PUNPCKLWD:
            tritonId = triton::arch::x86::ID_INS_PUNPCKLWD;
            break;

          case triton::extlibs::capstone::X86_INS_PXOR:
            tritonId = triton::arch::x86::ID_INS_PXOR;
            break;

          case triton::extlibs::capstone::X86_INS_MONITOR:
            tritonId = triton::arch::x86::ID_INS_MONITOR;
            break;

          case triton::extlibs::capstone::X86_INS_MONTMUL:
            tritonId = triton::arch::x86::ID_INS_MONTMUL;
            break;

          case triton::extlibs::capstone::X86_INS_MOV:
            tritonId = triton::arch::x86::ID_INS_MOV;
            break;

          case triton::extlibs::capstone::X86_INS_MOVABS:
            tritonId = triton::arch::x86::ID_INS_MOVABS;
            break;

          case triton::extlibs::capstone::X86_INS_MOVBE:
            tritonId = triton::arch::x86::ID_INS_MOVBE;
            break;

          case triton::extlibs::capstone::X86_INS_MOVDDUP:
            tritonId = triton::arch::x86::ID_INS_MOVDDUP;
            break;

          case triton::extlibs::capstone::X86_INS_MOVDQA:
            tritonId = triton::arch::x86::ID_INS_MOVDQA;
            break;

          case triton::extlibs::capstone::X86_INS_MOVDQU:
            tritonId = triton::arch::x86::ID_INS_MOVDQU;
            break;

          case triton::extlibs::capstone::X86_INS_MOVHLPS:
            tritonId = triton::arch::x86::ID_INS_MOVHLPS;
            break;

          case triton::extlibs::capstone::X86_INS_MOVHPD:
            tritonId = triton::arch::x86::ID_INS_MOVHPD;
            break;

          case triton::extlibs::capstone::X86_INS_MOVHPS:
            tritonId = triton::arch::x86::ID_INS_MOVHPS;
            break;

          case triton::extlibs::capstone::X86_INS_MOVLHPS:
            tritonId = triton::arch::x86::ID_INS_MOVLHPS;
            break;

          case triton::extlibs::capstone::X86_INS_MOVLPD:
            tritonId = triton::arch::x86::ID_INS_MOVLPD;
            break;

          case triton::extlibs::capstone::X86_INS_MOVLPS:
            tritonId = triton::arch::x86::ID_INS_MOVLPS;
            break;

          case triton::extlibs::capstone::X86_INS_MOVMSKPD:
            tritonId = triton::arch::x86::ID_INS_MOVMSKPD;
            break;

          case triton::extlibs::capstone::X86_INS_MOVMSKPS:
            tritonId = triton::arch::x86::ID_INS_MOVMSKPS;
            break;

          case triton::extlibs::capstone::X86_INS_MOVNTDQA:
            tritonId = triton::arch::x86::ID_INS_MOVNTDQA;
            break;

          case triton::extlibs::capstone::X86_INS_MOVNTDQ:
            tritonId = triton::arch::x86::ID_INS_MOVNTDQ;
            break;

          case triton::extlibs::capstone::X86_INS_MOVNTI:
            tritonId = triton::arch::x86::ID_INS_MOVNTI;
            break;

          case triton::extlibs::capstone::X86_INS_MOVNTPD:
            tritonId = triton::arch::x86::ID_INS_MOVNTPD;
            break;

          case triton::extlibs::capstone::X86_INS_MOVNTPS:
            tritonId = triton::arch::x86::ID_INS_MOVNTPS;
            break;

          case triton::extlibs::capstone::X86_INS_MOVNTSD:
            tritonId = triton::arch::x86::ID_INS_MOVNTSD;
            break;

          case triton::extlibs::capstone::X86_INS_MOVNTSS:
            tritonId = triton::arch::x86::ID_INS_MOVNTSS;
            break;

          case triton::extlibs::capstone::X86_INS_MOVSB:
            tritonId = triton::arch::x86::ID_INS_MOVSB;
            break;

          case triton::extlibs::capstone::X86_INS_MOVSD:
            tritonId = triton::arch::x86::ID_INS_MOVSD;
            break;

          case triton::extlibs::capstone::X86_INS_MOVSHDUP:
            tritonId = triton::arch::x86::ID_INS_MOVSHDUP;
            break;

          case triton::extlibs::capstone::X86_INS_MOVSLDUP:
            tritonId = triton::arch::x86::ID_INS_MOVSLDUP;
            break;

          case triton::extlibs::capstone::X86_INS_MOVSQ:
            tritonId = triton::arch::x86::ID_INS_MOVSQ;
            break;

          case triton::extlibs::capstone::X86_INS_MOVSS:
            tritonId = triton::arch::x86::ID_INS_MOVSS;
            break;

          case triton::extlibs::capstone::X86_INS_MOVSW:
            tritonId = triton::arch::x86::ID_INS_MOVSW;
            break;

          case triton::extlibs::capstone::X86_INS_MOVSX:
            tritonId = triton::arch::x86::ID_INS_MOVSX;
            break;

          case triton::extlibs::capstone::X86_INS_MOVSXD:
            tritonId = triton::arch::x86::ID_INS_MOVSXD;
            break;

          case triton::extlibs::capstone::X86_INS_MOVUPD:
            tritonId = triton::arch::x86::ID_INS_MOVUPD;
            break;

          case triton::extlibs::capstone::X86_INS_MOVUPS:
            tritonId = triton::arch::x86::ID_INS_MOVUPS;
            break;

          case triton::extlibs::capstone::X86_INS_MOVZX:
            tritonId = triton::arch::x86::ID_INS_MOVZX;
            break;

          case triton::extlibs::capstone::X86_INS_MPSADBW:
            tritonId = triton::arch::x86::ID_INS_MPSADBW;
            break;

          case triton::extlibs::capstone::X86_INS_MUL:
            tritonId = triton::arch::x86::ID_INS_MUL;
            break;

          case triton::extlibs::capstone::X86_INS_MULPD:
            tritonId = triton::arch::x86::ID_INS_MULPD;
            break;

          case triton::extlibs::capstone::X86_INS_MULPS:
            tritonId = triton::arch::x86::ID_INS_MULPS;
            break;

          case triton::extlibs::capstone::X86_INS_MULSD:
            tritonId = triton::arch::x86::ID_INS_MULSD;
            break;

          case triton::extlibs::capstone::X86_INS_MULSS:
            tritonId = triton::arch::x86::ID_INS_MULSS;
            break;

          case triton::extlibs::capstone::X86_INS_MULX:
            tritonId = triton::arch::x86::ID_INS_MULX;
            break;

          case triton::extlibs::capstone::X86_INS_FMUL:
            tritonId = triton::arch::x86::ID_INS_FMUL;
            break;

          case triton::extlibs::capstone::X86_INS_FIMUL:
            tritonId = triton::arch::x86::ID_INS_FIMUL;
            break;

          case triton::extlibs::capstone::X86_INS_FMULP:
            tritonId = triton::arch::x86::ID_INS_FMULP;
            break;

          case triton::extlibs::capstone::X86_INS_MWAIT:
            tritonId = triton::arch::x86::ID_INS_MWAIT;
            break;

          case triton::extlibs::capstone::X86_INS_NEG:
            tritonId = triton::arch::x86::ID_INS_NEG;
            break;

          case triton::extlibs::capstone::X86_INS_NOP:
            tritonId = triton::arch::x86::ID_INS_NOP;
            break;

          case triton::extlibs::capstone::X86_INS_NOT:
            tritonId = triton::arch::x86::ID_INS_NOT;
            break;

          case triton::extlibs::capstone::X86_INS_OUT:
            tritonId = triton::arch::x86::ID_INS_OUT;
            break;

          case triton::extlibs::capstone::X86_INS_OUTSB:
            tritonId = triton::arch::x86::ID_INS_OUTSB;
            break;

          case triton::extlibs::capstone::X86_INS_OUTSD:
            tritonId = triton::arch::x86::ID_INS_OUTSD;
            break;

          case triton::extlibs::capstone::X86_INS_OUTSW:
            tritonId = triton::arch::x86::ID_INS_OUTSW;
            break;

          case triton::extlibs::capstone::X86_INS_PACKUSDW:
            tritonId = triton::arch::x86::ID_INS_PACKUSDW;
            break;

          case triton::extlibs::capstone::X86_INS_PAUSE:
            tritonId = triton::arch::x86::ID_INS_PAUSE;
            break;

          case triton::extlibs::capstone::X86_INS_PAVGUSB:
            tritonId = triton::arch::x86::ID_INS_PAVGUSB;
            break;

          case triton::extlibs::capstone::X86_INS_PBLENDVB:
            tritonId = triton::arch::x86::ID_INS_PBLENDVB;
            break;

          case triton::extlibs::capstone::X86_INS_PBLENDW:
            tritonId = triton::arch::x86::ID_INS_PBLENDW;
            break;

          case triton::extlibs::capstone::X86_INS_PCLMULQDQ:
            tritonId = triton::arch::x86::ID_INS_PCLMULQDQ;
            break;

          case triton::extlibs::capstone::X86_INS_PCMPEQQ:
            tritonId = triton::arch::x86::ID_INS_PCMPEQQ;
            break;

          case triton::extlibs::capstone::X86_INS_PCMPESTRI:
            tritonId = triton::arch::x86::ID_INS_PCMPESTRI;
            break;

          case triton::extlibs::capstone::X86_INS_PCMPESTRM:
            tritonId = triton::arch::x86::ID_INS_PCMPESTRM;
            break;

          case triton::extlibs::capstone::X86_INS_PCMPGTQ:
            tritonId = triton::arch::x86::ID_INS_PCMPGTQ;
            break;

          case triton::extlibs::capstone::X86_INS_PCMPISTRI:
            tritonId = triton::arch::x86::ID_INS_PCMPISTRI;
            break;

          case triton::extlibs::capstone::X86_INS_PCMPISTRM:
            tritonId = triton::arch::x86::ID_INS_PCMPISTRM;
            break;

          case triton::extlibs::capstone::X86_INS_PDEP:
            tritonId = triton::arch::x86::ID_INS_PDEP;
            break;

          case triton::extlibs::capstone::X86_INS_PEXT:
            tritonId = triton::arch::x86::ID_INS_PEXT;
            break;

          case triton::extlibs::capstone::X86_INS_PEXTRB:
            tritonId = triton::arch::x86::ID_INS_PEXTRB;
            break;

          case triton::extlibs::capstone::X86_INS_PEXTRD:
            tritonId = triton::arch::x86::ID_INS_PEXTRD;
            break;

          case triton::extlibs::capstone::X86_INS_PEXTRQ:
            tritonId = triton::arch::x86::ID_INS_PEXTRQ;
            break;

          case triton::extlibs::capstone::X86_INS_PF2ID:
            tritonId = triton::arch::x86::ID_INS_PF2ID;
            break;

          case triton::extlibs::capstone::X86_INS_PF2IW:
            tritonId = triton::arch::x86::ID_INS_PF2IW;
            break;

          case triton::extlibs::capstone::X86_INS_PFACC:
            tritonId = triton::arch::x86::ID_INS_PFACC;
            break;

          case triton::extlibs::capstone::X86_INS_PFADD:
            tritonId = triton::arch::x86::ID_INS_PFADD;
            break;

          case triton::extlibs::capstone::X86_INS_PFCMPEQ:
            tritonId = triton::arch::x86::ID_INS_PFCMPEQ;
            break;

          case triton::extlibs::capstone::X86_INS_PFCMPGE:
            tritonId = triton::arch::x86::ID_INS_PFCMPGE;
            break;

          case triton::extlibs::capstone::X86_INS_PFCMPGT:
            tritonId = triton::arch::x86::ID_INS_PFCMPGT;
            break;

          case triton::extlibs::capstone::X86_INS_PFMAX:
            tritonId = triton::arch::x86::ID_INS_PFMAX;
            break;

          case triton::extlibs::capstone::X86_INS_PFMIN:
            tritonId = triton::arch::x86::ID_INS_PFMIN;
            break;

          case triton::extlibs::capstone::X86_INS_PFMUL:
            tritonId = triton::arch::x86::ID_INS_PFMUL;
            break;

          case triton::extlibs::capstone::X86_INS_PFNACC:
            tritonId = triton::arch::x86::ID_INS_PFNACC;
            break;

          case triton::extlibs::capstone::X86_INS_PFPNACC:
            tritonId = triton::arch::x86::ID_INS_PFPNACC;
            break;

          case triton::extlibs::capstone::X86_INS_PFRCPIT1:
            tritonId = triton::arch::x86::ID_INS_PFRCPIT1;
            break;

          case triton::extlibs::capstone::X86_INS_PFRCPIT2:
            tritonId = triton::arch::x86::ID_INS_PFRCPIT2;
            break;

          case triton::extlibs::capstone::X86_INS_PFRCP:
            tritonId = triton::arch::x86::ID_INS_PFRCP;
            break;

          case triton::extlibs::capstone::X86_INS_PFRSQIT1:
            tritonId = triton::arch::x86::ID_INS_PFRSQIT1;
            break;

          case triton::extlibs::capstone::X86_INS_PFRSQRT:
            tritonId = triton::arch::x86::ID_INS_PFRSQRT;
            break;

          case triton::extlibs::capstone::X86_INS_PFSUBR:
            tritonId = triton::arch::x86::ID_INS_PFSUBR;
            break;

          case triton::extlibs::capstone::X86_INS_PFSUB:
            tritonId = triton::arch::x86::ID_INS_PFSUB;
            break;

          case triton::extlibs::capstone::X86_INS_PHMINPOSUW:
            tritonId = triton::arch::x86::ID_INS_PHMINPOSUW;
            break;

          case triton::extlibs::capstone::X86_INS_PI2FD:
            tritonId = triton::arch::x86::ID_INS_PI2FD;
            break;

          case triton::extlibs::capstone::X86_INS_PI2FW:
            tritonId = triton::arch::x86::ID_INS_PI2FW;
            break;

          case triton::extlibs::capstone::X86_INS_PINSRB:
            tritonId = triton::arch::x86::ID_INS_PINSRB;
            break;

          case triton::extlibs::capstone::X86_INS_PINSRD:
            tritonId = triton::arch::x86::ID_INS_PINSRD;
            break;

          case triton::extlibs::capstone::X86_INS_PINSRQ:
            tritonId = triton::arch::x86::ID_INS_PINSRQ;
            break;

          case triton::extlibs::capstone::X86_INS_PMAXSB:
            tritonId = triton::arch::x86::ID_INS_PMAXSB;
            break;

          case triton::extlibs::capstone::X86_INS_PMAXSD:
            tritonId = triton::arch::x86::ID_INS_PMAXSD;
            break;

          case triton::extlibs::capstone::X86_INS_PMAXUD:
            tritonId = triton::arch::x86::ID_INS_PMAXUD;
            break;

          case triton::extlibs::capstone::X86_INS_PMAXUW:
            tritonId = triton::arch::x86::ID_INS_PMAXUW;
            break;

          case triton::extlibs::capstone::X86_INS_PMINSB:
            tritonId = triton::arch::x86::ID_INS_PMINSB;
            break;

          case triton::extlibs::capstone::X86_INS_PMINSD:
            tritonId = triton::arch::x86::ID_INS_PMINSD;
            break;

          case triton::extlibs::capstone::X86_INS_PMINUD:
            tritonId = triton::arch::x86::ID_INS_PMINUD;
            break;

          case triton::extlibs::capstone::X86_INS_PMINUW:
            tritonId = triton::arch::x86::ID_INS_PMINUW;
            break;

          case triton::extlibs::capstone::X86_INS_PMOVSXBD:
            tritonId = triton::arch::x86::ID_INS_PMOVSXBD;
            break;

          case triton::extlibs::capstone::X86_INS_PMOVSXBQ:
            tritonId = triton::arch::x86::ID_INS_PMOVSXBQ;
            break;

          case triton::extlibs::capstone::X86_INS_PMOVSXBW:
            tritonId = triton::arch::x86::ID_INS_PMOVSXBW;
            break;

          case triton::extlibs::capstone::X86_INS_PMOVSXDQ:
            tritonId = triton::arch::x86::ID_INS_PMOVSXDQ;
            break;

          case triton::extlibs::capstone::X86_INS_PMOVSXWD:
            tritonId = triton::arch::x86::ID_INS_PMOVSXWD;
            break;

          case triton::extlibs::capstone::X86_INS_PMOVSXWQ:
            tritonId = triton::arch::x86::ID_INS_PMOVSXWQ;
            break;

          case triton::extlibs::capstone::X86_INS_PMOVZXBD:
            tritonId = triton::arch::x86::ID_INS_PMOVZXBD;
            break;

          case triton::extlibs::capstone::X86_INS_PMOVZXBQ:
            tritonId = triton::arch::x86::ID_INS_PMOVZXBQ;
            break;

          case triton::extlibs::capstone::X86_INS_PMOVZXBW:
            tritonId = triton::arch::x86::ID_INS_PMOVZXBW;
            break;

          case triton::extlibs::capstone::X86_INS_PMOVZXDQ:
            tritonId = triton::arch::x86::ID_INS_PMOVZXDQ;
            break;

          case triton::extlibs::capstone::X86_INS_PMOVZXWD:
            tritonId = triton::arch::x86::ID_INS_PMOVZXWD;
            break;

          case triton::extlibs::capstone::X86_INS_PMOVZXWQ:
            tritonId = triton::arch::x86::ID_INS_PMOVZXWQ;
            break;

          case triton::extlibs::capstone::X86_INS_PMULDQ:
            tritonId = triton::arch::x86::ID_INS_PMULDQ;
            break;

          case triton::extlibs::capstone::X86_INS_PMULHRW:
            tritonId = triton::arch::x86::ID_INS_PMULHRW;
            break;

          case triton::extlibs::capstone::X86_INS_PMULLD:
            tritonId = triton::arch::x86::ID_INS_PMULLD;
            break;

          case triton::extlibs::capstone::X86_INS_POP:
            tritonId = triton::arch::x86::ID_INS_POP;
            break;

          case triton::extlibs::capstone::X86_INS_POPAW:
            tritonId = triton::arch::x86::ID_INS_POPAW;
            break;

          case triton::extlibs::capstone::X86_INS_POPAL:
            tritonId = triton::arch::x86::ID_INS_POPAL;
            break;

          case triton::extlibs::capstone::X86_INS_POPCNT:
            tritonId = triton::arch::x86::ID_INS_POPCNT;
            break;

          case triton::extlibs::capstone::X86_INS_POPF:
            tritonId = triton::arch::x86::ID_INS_POPF;
            break;

          case triton::extlibs::capstone::X86_INS_POPFD:
            tritonId = triton::arch::x86::ID_INS_POPFD;
            break;

          case triton::extlibs::capstone::X86_INS_POPFQ:
            tritonId = triton::arch::x86::ID_INS_POPFQ;
            break;

          case triton::extlibs::capstone::X86_INS_PREFETCH:
            tritonId = triton::arch::x86::ID_INS_PREFETCH;
            break;

          case triton::extlibs::capstone::X86_INS_PREFETCHNTA:
            tritonId = triton::arch::x86::ID_INS_PREFETCHNTA;
            break;

          case triton::extlibs::capstone::X86_INS_PREFETCHT0:
            tritonId = triton::arch::x86::ID_INS_PREFETCHT0;
            break;

          case triton::extlibs::capstone::X86_INS_PREFETCHT1:
            tritonId = triton::arch::x86::ID_INS_PREFETCHT1;
            break;

          case triton::extlibs::capstone::X86_INS_PREFETCHT2:
            tritonId = triton::arch::x86::ID_INS_PREFETCHT2;
            break;

          case triton::extlibs::capstone::X86_INS_PREFETCHW:
            tritonId = triton::arch::x86::ID_INS_PREFETCHW;
            break;

          case triton::extlibs::capstone::X86_INS_PSHUFD:
            tritonId = triton::arch::x86::ID_INS_PSHUFD;
            break;

          case triton::extlibs::capstone::X86_INS_PSHUFHW:
            tritonId = triton::arch::x86::ID_INS_PSHUFHW;
            break;

          case triton::extlibs::capstone::X86_INS_PSHUFLW:
            tritonId = triton::arch::x86::ID_INS_PSHUFLW;
            break;

          case triton::extlibs::capstone::X86_INS_PSLLDQ:
            tritonId = triton::arch::x86::ID_INS_PSLLDQ;
            break;

          case triton::extlibs::capstone::X86_INS_PSRLDQ:
            tritonId = triton::arch::x86::ID_INS_PSRLDQ;
            break;

          case triton::extlibs::capstone::X86_INS_PSWAPD:
            tritonId = triton::arch::x86::ID_INS_PSWAPD;
            break;

          case triton::extlibs::capstone::X86_INS_PTEST:
            tritonId = triton::arch::x86::ID_INS_PTEST;
            break;

          case triton::extlibs::capstone::X86_INS_PUNPCKHQDQ:
            tritonId = triton::arch::x86::ID_INS_PUNPCKHQDQ;
            break;

          case triton::extlibs::capstone::X86_INS_PUNPCKLQDQ:
            tritonId = triton::arch::x86::ID_INS_PUNPCKLQDQ;
            break;

          case triton::extlibs::capstone::X86_INS_PUSH:
            tritonId = triton::arch::x86::ID_INS_PUSH;
            break;

          case triton::extlibs::capstone::X86_INS_PUSHAW:
            tritonId = triton::arch::x86::ID_INS_PUSHAW;
            break;

          case triton::extlibs::capstone::X86_INS_PUSHAL:
            tritonId = triton::arch::x86::ID_INS_PUSHAL;
            break;

          case triton::extlibs::capstone::X86_INS_PUSHF:
            tritonId = triton::arch::x86::ID_INS_PUSHF;
            break;

          case triton::extlibs::capstone::X86_INS_PUSHFD:
            tritonId = triton::arch::x86::ID_INS_PUSHFD;
            break;

          case triton::extlibs::capstone::X86_INS_PUSHFQ:
            tritonId = triton::arch::x86::ID_INS_PUSHFQ;
            break;

          case triton::extlibs::capstone::X86_INS_RCL:
            tritonId = triton::arch::x86::ID_INS_RCL;
            break;

          case triton::extlibs::capstone::X86_INS_RCPPS:
            tritonId = triton::arch::x86::ID_INS_RCPPS;
            break;

          case triton::extlibs::capstone::X86_INS_RCPSS:
            tritonId = triton::arch::x86::ID_INS_RCPSS;
            break;

          case triton::extlibs::capstone::X86_INS_RCR:
            tritonId = triton::arch::x86::ID_INS_RCR;
            break;

          case triton::extlibs::capstone::X86_INS_RDFSBASE:
            tritonId = triton::arch::x86::ID_INS_RDFSBASE;
            break;

          case triton::extlibs::capstone::X86_INS_RDGSBASE:
            tritonId = triton::arch::x86::ID_INS_RDGSBASE;
            break;

          case triton::extlibs::capstone::X86_INS_RDMSR:
            tritonId = triton::arch::x86::ID_INS_RDMSR;
            break;

          case triton::extlibs::capstone::X86_INS_RDPMC:
            tritonId = triton::arch::x86::ID_INS_RDPMC;
            break;

          case triton::extlibs::capstone::X86_INS_RDRAND:
            tritonId = triton::arch::x86::ID_INS_RDRAND;
            break;

          case triton::extlibs::capstone::X86_INS_RDSEED:
            tritonId = triton::arch::x86::ID_INS_RDSEED;
            break;

          case triton::extlibs::capstone::X86_INS_RDTSC:
            tritonId = triton::arch::x86::ID_INS_RDTSC;
            break;

          case triton::extlibs::capstone::X86_INS_RDTSCP:
            tritonId = triton::arch::x86::ID_INS_RDTSCP;
            break;

          case triton::extlibs::capstone::X86_INS_ROL:
            tritonId = triton::arch::x86::ID_INS_ROL;
            break;

          case triton::extlibs::capstone::X86_INS_ROR:
            tritonId = triton::arch::x86::ID_INS_ROR;
            break;

          case triton::extlibs::capstone::X86_INS_RORX:
            tritonId = triton::arch::x86::ID_INS_RORX;
            break;

          case triton::extlibs::capstone::X86_INS_ROUNDPD:
            tritonId = triton::arch::x86::ID_INS_ROUNDPD;
            break;

          case triton::extlibs::capstone::X86_INS_ROUNDPS:
            tritonId = triton::arch::x86::ID_INS_ROUNDPS;
            break;

          case triton::extlibs::capstone::X86_INS_ROUNDSD:
            tritonId = triton::arch::x86::ID_INS_ROUNDSD;
            break;

          case triton::extlibs::capstone::X86_INS_ROUNDSS:
            tritonId = triton::arch::x86::ID_INS_ROUNDSS;
            break;

          case triton::extlibs::capstone::X86_INS_RSM:
            tritonId = triton::arch::x86::ID_INS_RSM;
            break;

          case triton::extlibs::capstone::X86_INS_RSQRTPS:
            tritonId = triton::arch::x86::ID_INS_RSQRTPS;
            break;

          case triton::extlibs::capstone::X86_INS_RSQRTSS:
            tritonId = triton::arch::x86::ID_INS_RSQRTSS;
            break;

          case triton::extlibs::capstone::X86_INS_SAHF:
            tritonId = triton::arch::x86::ID_INS_SAHF;
            break;

          case triton::extlibs::capstone::X86_INS_SAL:
            tritonId = triton::arch::x86::ID_INS_SAL;
            break;

          case triton::extlibs::capstone::X86_INS_SALC:
            tritonId = triton::arch::x86::ID_INS_SALC;
            break;

          case triton::extlibs::capstone::X86_INS_SAR:
            tritonId = triton::arch::x86::ID_INS_SAR;
            break;

          case triton::extlibs::capstone::X86_INS_SARX:
            tritonId = triton::arch::x86::ID_INS_SARX;
            break;

          case triton::extlibs::capstone::X86_INS_SBB:
            tritonId = triton::arch::x86::ID_INS_SBB;
            break;

          case triton::extlibs::capstone::X86_INS_SCASB:
            tritonId = triton::arch::x86::ID_INS_SCASB;
            break;

          case triton::extlibs::capstone::X86_INS_SCASD:
            tritonId = triton::arch::x86::ID_INS_SCASD;
            break;

          case triton::extlibs::capstone::X86_INS_SCASQ:
            tritonId = triton::arch::x86::ID_INS_SCASQ;
            break;

          case triton::extlibs::capstone::X86_INS_SCASW:
            tritonId = triton::arch::x86::ID_INS_SCASW;
            break;

          case triton::extlibs::capstone::X86_INS_SETAE:
            tritonId = triton::arch::x86::ID_INS_SETAE;
            break;

          case triton::extlibs::capstone::X86_INS_SETA:
            tritonId = triton::arch::x86::ID_INS_SETA;
            break;

          case triton::extlibs::capstone::X86_INS_SETBE:
            tritonId = triton::arch::x86::ID_INS_SETBE;
            break;

          case triton::extlibs::capstone::X86_INS_SETB:
            tritonId = triton::arch::x86::ID_INS_SETB;
            break;

          case triton::extlibs::capstone::X86_INS_SETE:
            tritonId = triton::arch::x86::ID_INS_SETE;
            break;

          case triton::extlibs::capstone::X86_INS_SETGE:
            tritonId = triton::arch::x86::ID_INS_SETGE;
            break;

          case triton::extlibs::capstone::X86_INS_SETG:
            tritonId = triton::arch::x86::ID_INS_SETG;
            break;

          case triton::extlibs::capstone::X86_INS_SETLE:
            tritonId = triton::arch::x86::ID_INS_SETLE;
            break;

          case triton::extlibs::capstone::X86_INS_SETL:
            tritonId = triton::arch::x86::ID_INS_SETL;
            break;

          case triton::extlibs::capstone::X86_INS_SETNE:
            tritonId = triton::arch::x86::ID_INS_SETNE;
            break;

          case triton::extlibs::capstone::X86_INS_SETNO:
            tritonId = triton::arch::x86::ID_INS_SETNO;
            break;

          case triton::extlibs::capstone::X86_INS_SETNP:
            tritonId = triton::arch::x86::ID_INS_SETNP;
            break;

          case triton::extlibs::capstone::X86_INS_SETNS:
            tritonId = triton::arch::x86::ID_INS_SETNS;
            break;

          case triton::extlibs::capstone::X86_INS_SETO:
            tritonId = triton::arch::x86::ID_INS_SETO;
            break;

          case triton::extlibs::capstone::X86_INS_SETP:
            tritonId = triton::arch::x86::ID_INS_SETP;
            break;

          case triton::extlibs::capstone::X86_INS_SETS:
            tritonId = triton::arch::x86::ID_INS_SETS;
            break;

          case triton::extlibs::capstone::X86_INS_SFENCE:
            tritonId = triton::arch::x86::ID_INS_SFENCE;
            break;

          case triton::extlibs::capstone::X86_INS_SGDT:
            tritonId = triton::arch::x86::ID_INS_SGDT;
            break;

          case triton::extlibs::capstone::X86_INS_SHA1MSG1:
            tritonId = triton::arch::x86::ID_INS_SHA1MSG1;
            break;

          case triton::extlibs::capstone::X86_INS_SHA1MSG2:
            tritonId = triton::arch::x86::ID_INS_SHA1MSG2;
            break;

          case triton::extlibs::capstone::X86_INS_SHA1NEXTE:
            tritonId = triton::arch::x86::ID_INS_SHA1NEXTE;
            break;

          case triton::extlibs::capstone::X86_INS_SHA1RNDS4:
            tritonId = triton::arch::x86::ID_INS_SHA1RNDS4;
            break;

          case triton::extlibs::capstone::X86_INS_SHA256MSG1:
            tritonId = triton::arch::x86::ID_INS_SHA256MSG1;
            break;

          case triton::extlibs::capstone::X86_INS_SHA256MSG2:
            tritonId = triton::arch::x86::ID_INS_SHA256MSG2;
            break;

          case triton::extlibs::capstone::X86_INS_SHA256RNDS2:
            tritonId = triton::arch::x86::ID_INS_SHA256RNDS2;
            break;

          case triton::extlibs::capstone::X86_INS_SHL:
            tritonId = triton::arch::x86::ID_INS_SHL;
            break;

          case triton::extlibs::capstone::X86_INS_SHLD:
            tritonId = triton::arch::x86::ID_INS_SHLD;
            break;

          case triton::extlibs::capstone::X86_INS_SHLX:
            tritonId = triton::arch::x86::ID_INS_SHLX;
            break;

          case triton::extlibs::capstone::X86_INS_SHR:
            tritonId = triton::arch::x86::ID_INS_SHR;
            break;

          case triton::extlibs::capstone::X86_INS_SHRD:
            tritonId = triton::arch::x86::ID_INS_SHRD;
            break;

          case triton::extlibs::capstone::X86_INS_SHRX:
            tritonId = triton::arch::x86::ID_INS_SHRX;
            break;

          case triton::extlibs::capstone::X86_INS_SHUFPD:
            tritonId = triton::arch::x86::ID_INS_SHUFPD;
            break;

          case triton::extlibs::capstone::X86_INS_SHUFPS:
            tritonId = triton::arch::x86::ID_INS_SHUFPS;
            break;

          case triton::extlibs::capstone::X86_INS_SIDT:
            tritonId = triton::arch::x86::ID_INS_SIDT;
            break;

          case triton::extlibs::capstone::X86_INS_FSIN:
            tritonId = triton::arch::x86::ID_INS_FSIN;
            break;

          case triton::extlibs::capstone::X86_INS_SKINIT:
            tritonId = triton::arch::x86::ID_INS_SKINIT;
            break;

          case triton::extlibs::capstone::X86_INS_SLDT:
            tritonId = triton::arch::x86::ID_INS_SLDT;
            break;

          case triton::extlibs::capstone::X86_INS_SMSW:
            tritonId = triton::arch::x86::ID_INS_SMSW;
            break;

          case triton::extlibs::capstone::X86_INS_SQRTPD:
            tritonId = triton::arch::x86::ID_INS_SQRTPD;
            break;

          case triton::extlibs::capstone::X86_INS_SQRTPS:
            tritonId = triton::arch::x86::ID_INS_SQRTPS;
            break;

          case triton::extlibs::capstone::X86_INS_SQRTSD:
            tritonId = triton::arch::x86::ID_INS_SQRTSD;
            break;

          case triton::extlibs::capstone::X86_INS_SQRTSS:
            tritonId = triton::arch::x86::ID_INS_SQRTSS;
            break;

          case triton::extlibs::capstone::X86_INS_FSQRT:
            tritonId = triton::arch::x86::ID_INS_FSQRT;
            break;

          case triton::extlibs::capstone::X86_INS_STAC:
            tritonId = triton::arch::x86::ID_INS_STAC;
            break;

          case triton::extlibs::capstone::X86_INS_STC:
            tritonId = triton::arch::x86::ID_INS_STC;
            break;

          case triton::extlibs::capstone::X86_INS_STD:
            tritonId = triton::arch::x86::ID_INS_STD;
            break;

          case triton::extlibs::capstone::X86_INS_STGI:
            tritonId = triton::arch::x86::ID_INS_STGI;
            break;

          case triton::extlibs::capstone::X86_INS_STI:
            tritonId = triton::arch::x86::ID_INS_STI;
            break;

          case triton::extlibs::capstone::X86_INS_STMXCSR:
            tritonId = triton::arch::x86::ID_INS_STMXCSR;
            break;

          case triton::extlibs::capstone::X86_INS_STOSB:
            tritonId = triton::arch::x86::ID_INS_STOSB;
            break;

          case triton::extlibs::capstone::X86_INS_STOSD:
            tritonId = triton::arch::x86::ID_INS_STOSD;
            break;

          case triton::extlibs::capstone::X86_INS_STOSQ:
            tritonId = triton::arch::x86::ID_INS_STOSQ;
            break;

          case triton::extlibs::capstone::X86_INS_STOSW:
            tritonId = triton::arch::x86::ID_INS_STOSW;
            break;

          case triton::extlibs::capstone::X86_INS_STR:
            tritonId = triton::arch::x86::ID_INS_STR;
            break;

          case triton::extlibs::capstone::X86_INS_FST:
            tritonId = triton::arch::x86::ID_INS_FST;
            break;

          case triton::extlibs::capstone::X86_INS_FSTP:
            tritonId = triton::arch::x86::ID_INS_FSTP;
            break;

          case triton::extlibs::capstone::X86_INS_FSTPNCE:
            tritonId = triton::arch::x86::ID_INS_FSTPNCE;
            break;

          case triton::extlibs::capstone::X86_INS_SUBPD:
            tritonId = triton::arch::x86::ID_INS_SUBPD;
            break;

          case triton::extlibs::capstone::X86_INS_SUBPS:
            tritonId = triton::arch::x86::ID_INS_SUBPS;
            break;

          case triton::extlibs::capstone::X86_INS_FSUBR:
            tritonId = triton::arch::x86::ID_INS_FSUBR;
            break;

          case triton::extlibs::capstone::X86_INS_FISUBR:
            tritonId = triton::arch::x86::ID_INS_FISUBR;
            break;

          case triton::extlibs::capstone::X86_INS_FSUBRP:
            tritonId = triton::arch::x86::ID_INS_FSUBRP;
            break;

          case triton::extlibs::capstone::X86_INS_SUBSD:
            tritonId = triton::arch::x86::ID_INS_SUBSD;
            break;

          case triton::extlibs::capstone::X86_INS_SUBSS:
            tritonId = triton::arch::x86::ID_INS_SUBSS;
            break;

          case triton::extlibs::capstone::X86_INS_FSUB:
            tritonId = triton::arch::x86::ID_INS_FSUB;
            break;

          case triton::extlibs::capstone::X86_INS_FISUB:
            tritonId = triton::arch::x86::ID_INS_FISUB;
            break;

          case triton::extlibs::capstone::X86_INS_FSUBP:
            tritonId = triton::arch::x86::ID_INS_FSUBP;
            break;

          case triton::extlibs::capstone::X86_INS_SWAPGS:
            tritonId = triton::arch::x86::ID_INS_SWAPGS;
            break;

          case triton::extlibs::capstone::X86_INS_SYSCALL:
            tritonId = triton::arch::x86::ID_INS_SYSCALL;
            break;

          case triton::extlibs::capstone::X86_INS_SYSENTER:
            tritonId = triton::arch::x86::ID_INS_SYSENTER;
            break;

          case triton::extlibs::capstone::X86_INS_SYSEXIT:
            tritonId = triton::arch::x86::ID_INS_SYSEXIT;
            break;

          case triton::extlibs::capstone::X86_INS_SYSRET:
            tritonId = triton::arch::x86::ID_INS_SYSRET;
            break;

          case triton::extlibs::capstone::X86_INS_T1MSKC:
            tritonId = triton::arch::x86::ID_INS_T1MSKC;
            break;

          case triton::extlibs::capstone::X86_INS_TEST:
            tritonId = triton::arch::x86::ID_INS_TEST;
            break;

          case triton::extlibs::capstone::X86_INS_UD2:
            tritonId = triton::arch::x86::ID_INS_UD2;
            break;

          case triton::extlibs::capstone::X86_INS_FTST:
            tritonId = triton::arch::x86::ID_INS_FTST;
            break;

          case triton::extlibs::capstone::X86_INS_TZCNT:
            tritonId = triton::arch::x86::ID_INS_TZCNT;
            break;

          case triton::extlibs::capstone::X86_INS_TZMSK:
            tritonId = triton::arch::x86::ID_INS_TZMSK;
            break;

          case triton::extlibs::capstone::X86_INS_FUCOMPI:
            tritonId = triton::arch::x86::ID_INS_FUCOMPI;
            break;

          case triton::extlibs::capstone::X86_INS_FUCOMI:
            tritonId = triton::arch::x86::ID_INS_FUCOMI;
            break;

          case triton::extlibs::capstone::X86_INS_FUCOMPP:
            tritonId = triton::arch::x86::ID_INS_FUCOMPP;
            break;

          case triton::extlibs::capstone::X86_INS_FUCOMP:
            tritonId = triton::arch::x86::ID_INS_FUCOMP;
            break;

          case triton::extlibs::capstone::X86_INS_FUCOM:
            tritonId = triton::arch::x86::ID_INS_FUCOM;
            break;

          case triton::extlibs::capstone::X86_INS_UD2B:
            tritonId = triton::arch::x86::ID_INS_UD2B;
            break;

          case triton::extlibs::capstone::X86_INS_UNPCKHPD:
            tritonId = triton::arch::x86::ID_INS_UNPCKHPD;
            break;

          case triton::extlibs::capstone::X86_INS_UNPCKHPS:
            tritonId = triton::arch::x86::ID_INS_UNPCKHPS;
            break;

          case triton::extlibs::capstone::X86_INS_UNPCKLPD:
            tritonId = triton::arch::x86::ID_INS_UNPCKLPD;
            break;

          case triton::extlibs::capstone::X86_INS_UNPCKLPS:
            tritonId = triton::arch::x86::ID_INS_UNPCKLPS;
            break;

          case triton::extlibs::capstone::X86_INS_VADDPD:
            tritonId = triton::arch::x86::ID_INS_VADDPD;
            break;

          case triton::extlibs::capstone::X86_INS_VADDPS:
            tritonId = triton::arch::x86::ID_INS_VADDPS;
            break;

          case triton::extlibs::capstone::X86_INS_VADDSD:
            tritonId = triton::arch::x86::ID_INS_VADDSD;
            break;

          case triton::extlibs::capstone::X86_INS_VADDSS:
            tritonId = triton::arch::x86::ID_INS_VADDSS;
            break;

          case triton::extlibs::capstone::X86_INS_VADDSUBPD:
            tritonId = triton::arch::x86::ID_INS_VADDSUBPD;
            break;

          case triton::extlibs::capstone::X86_INS_VADDSUBPS:
            tritonId = triton::arch::x86::ID_INS_VADDSUBPS;
            break;

          case triton::extlibs::capstone::X86_INS_VAESDECLAST:
            tritonId = triton::arch::x86::ID_INS_VAESDECLAST;
            break;

          case triton::extlibs::capstone::X86_INS_VAESDEC:
            tritonId = triton::arch::x86::ID_INS_VAESDEC;
            break;

          case triton::extlibs::capstone::X86_INS_VAESENCLAST:
            tritonId = triton::arch::x86::ID_INS_VAESENCLAST;
            break;

          case triton::extlibs::capstone::X86_INS_VAESENC:
            tritonId = triton::arch::x86::ID_INS_VAESENC;
            break;

          case triton::extlibs::capstone::X86_INS_VAESIMC:
            tritonId = triton::arch::x86::ID_INS_VAESIMC;
            break;

          case triton::extlibs::capstone::X86_INS_VAESKEYGENASSIST:
            tritonId = triton::arch::x86::ID_INS_VAESKEYGENASSIST;
            break;

          case triton::extlibs::capstone::X86_INS_VALIGND:
            tritonId = triton::arch::x86::ID_INS_VALIGND;
            break;

          case triton::extlibs::capstone::X86_INS_VALIGNQ:
            tritonId = triton::arch::x86::ID_INS_VALIGNQ;
            break;

          case triton::extlibs::capstone::X86_INS_VANDNPD:
            tritonId = triton::arch::x86::ID_INS_VANDNPD;
            break;

          case triton::extlibs::capstone::X86_INS_VANDNPS:
            tritonId = triton::arch::x86::ID_INS_VANDNPS;
            break;

          case triton::extlibs::capstone::X86_INS_VANDPD:
            tritonId = triton::arch::x86::ID_INS_VANDPD;
            break;

          case triton::extlibs::capstone::X86_INS_VANDPS:
            tritonId = triton::arch::x86::ID_INS_VANDPS;
            break;

          case triton::extlibs::capstone::X86_INS_VBLENDMPD:
            tritonId = triton::arch::x86::ID_INS_VBLENDMPD;
            break;

          case triton::extlibs::capstone::X86_INS_VBLENDMPS:
            tritonId = triton::arch::x86::ID_INS_VBLENDMPS;
            break;

          case triton::extlibs::capstone::X86_INS_VBLENDPD:
            tritonId = triton::arch::x86::ID_INS_VBLENDPD;
            break;

          case triton::extlibs::capstone::X86_INS_VBLENDPS:
            tritonId = triton::arch::x86::ID_INS_VBLENDPS;
            break;

          case triton::extlibs::capstone::X86_INS_VBLENDVPD:
            tritonId = triton::arch::x86::ID_INS_VBLENDVPD;
            break;

          case triton::extlibs::capstone::X86_INS_VBLENDVPS:
            tritonId = triton::arch::x86::ID_INS_VBLENDVPS;
            break;

          case triton::extlibs::capstone::X86_INS_VBROADCASTF128:
            tritonId = triton::arch::x86::ID_INS_VBROADCASTF128;
            break;

          case triton::extlibs::capstone::X86_INS_VBROADCASTI128:
            tritonId = triton::arch::x86::ID_INS_VBROADCASTI128;
            break;

          case triton::extlibs::capstone::X86_INS_VBROADCASTI32X4:
            tritonId = triton::arch::x86::ID_INS_VBROADCASTI32X4;
            break;

          case triton::extlibs::capstone::X86_INS_VBROADCASTI64X4:
            tritonId = triton::arch::x86::ID_INS_VBROADCASTI64X4;
            break;

          case triton::extlibs::capstone::X86_INS_VBROADCASTSD:
            tritonId = triton::arch::x86::ID_INS_VBROADCASTSD;
            break;

          case triton::extlibs::capstone::X86_INS_VBROADCASTSS:
            tritonId = triton::arch::x86::ID_INS_VBROADCASTSS;
            break;

          case triton::extlibs::capstone::X86_INS_VCMPPD:
            tritonId = triton::arch::x86::ID_INS_VCMPPD;
            break;

          case triton::extlibs::capstone::X86_INS_VCMPPS:
            tritonId = triton::arch::x86::ID_INS_VCMPPS;
            break;

          case triton::extlibs::capstone::X86_INS_VCMPSD:
            tritonId = triton::arch::x86::ID_INS_VCMPSD;
            break;

          case triton::extlibs::capstone::X86_INS_VCMPSS:
            tritonId = triton::arch::x86::ID_INS_VCMPSS;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTDQ2PD:
            tritonId = triton::arch::x86::ID_INS_VCVTDQ2PD;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTDQ2PS:
            tritonId = triton::arch::x86::ID_INS_VCVTDQ2PS;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTPD2DQX:
            tritonId = triton::arch::x86::ID_INS_VCVTPD2DQX;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTPD2DQ:
            tritonId = triton::arch::x86::ID_INS_VCVTPD2DQ;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTPD2PSX:
            tritonId = triton::arch::x86::ID_INS_VCVTPD2PSX;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTPD2PS:
            tritonId = triton::arch::x86::ID_INS_VCVTPD2PS;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTPD2UDQ:
            tritonId = triton::arch::x86::ID_INS_VCVTPD2UDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTPH2PS:
            tritonId = triton::arch::x86::ID_INS_VCVTPH2PS;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTPS2DQ:
            tritonId = triton::arch::x86::ID_INS_VCVTPS2DQ;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTPS2PD:
            tritonId = triton::arch::x86::ID_INS_VCVTPS2PD;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTPS2PH:
            tritonId = triton::arch::x86::ID_INS_VCVTPS2PH;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTPS2UDQ:
            tritonId = triton::arch::x86::ID_INS_VCVTPS2UDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTSD2SI:
            tritonId = triton::arch::x86::ID_INS_VCVTSD2SI;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTSD2USI:
            tritonId = triton::arch::x86::ID_INS_VCVTSD2USI;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTSS2SI:
            tritonId = triton::arch::x86::ID_INS_VCVTSS2SI;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTSS2USI:
            tritonId = triton::arch::x86::ID_INS_VCVTSS2USI;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTTPD2DQX:
            tritonId = triton::arch::x86::ID_INS_VCVTTPD2DQX;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTTPD2DQ:
            tritonId = triton::arch::x86::ID_INS_VCVTTPD2DQ;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTTPD2UDQ:
            tritonId = triton::arch::x86::ID_INS_VCVTTPD2UDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTTPS2DQ:
            tritonId = triton::arch::x86::ID_INS_VCVTTPS2DQ;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTTPS2UDQ:
            tritonId = triton::arch::x86::ID_INS_VCVTTPS2UDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTUDQ2PD:
            tritonId = triton::arch::x86::ID_INS_VCVTUDQ2PD;
            break;

          case triton::extlibs::capstone::X86_INS_VCVTUDQ2PS:
            tritonId = triton::arch::x86::ID_INS_VCVTUDQ2PS;
            break;

          case triton::extlibs::capstone::X86_INS_VDIVPD:
            tritonId = triton::arch::x86::ID_INS_VDIVPD;
            break;

          case triton::extlibs::capstone::X86_INS_VDIVPS:
            tritonId = triton::arch::x86::ID_INS_VDIVPS;
            break;

          case triton::extlibs::capstone::X86_INS_VDIVSD:
            tritonId = triton::arch::x86::ID_INS_VDIVSD;
            break;

          case triton::extlibs::capstone::X86_INS_VDIVSS:
            tritonId = triton::arch::x86::ID_INS_VDIVSS;
            break;

          case triton::extlibs::capstone::X86_INS_VDPPD:
            tritonId = triton::arch::x86::ID_INS_VDPPD;
            break;

          case triton::extlibs::capstone::X86_INS_VDPPS:
            tritonId = triton::arch::x86::ID_INS_VDPPS;
            break;

          case triton::extlibs::capstone::X86_INS_VERR:
            tritonId = triton::arch::x86::ID_INS_VERR;
            break;

          case triton::extlibs::capstone::X86_INS_VERW:
            tritonId = triton::arch::x86::ID_INS_VERW;
            break;

          case triton::extlibs::capstone::X86_INS_VEXTRACTF128:
            tritonId = triton::arch::x86::ID_INS_VEXTRACTF128;
            break;

          case triton::extlibs::capstone::X86_INS_VEXTRACTF32X4:
            tritonId = triton::arch::x86::ID_INS_VEXTRACTF32X4;
            break;

          case triton::extlibs::capstone::X86_INS_VEXTRACTF64X4:
            tritonId = triton::arch::x86::ID_INS_VEXTRACTF64X4;
            break;

          case triton::extlibs::capstone::X86_INS_VEXTRACTI128:
            tritonId = triton::arch::x86::ID_INS_VEXTRACTI128;
            break;

          case triton::extlibs::capstone::X86_INS_VEXTRACTI32X4:
            tritonId = triton::arch::x86::ID_INS_VEXTRACTI32X4;
            break;

          case triton::extlibs::capstone::X86_INS_VEXTRACTI64X4:
            tritonId = triton::arch::x86::ID_INS_VEXTRACTI64X4;
            break;

          case triton::extlibs::capstone::X86_INS_VEXTRACTPS:
            tritonId = triton::arch::x86::ID_INS_VEXTRACTPS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADD132PD:
            tritonId = triton::arch::x86::ID_INS_VFMADD132PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADD132PS:
            tritonId = triton::arch::x86::ID_INS_VFMADD132PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADD213PD:
            tritonId = triton::arch::x86::ID_INS_VFMADD213PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADD213PS:
            tritonId = triton::arch::x86::ID_INS_VFMADD213PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADDPD:
            tritonId = triton::arch::x86::ID_INS_VFMADDPD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADD231PD:
            tritonId = triton::arch::x86::ID_INS_VFMADD231PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADDPS:
            tritonId = triton::arch::x86::ID_INS_VFMADDPS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADD231PS:
            tritonId = triton::arch::x86::ID_INS_VFMADD231PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADDSD:
            tritonId = triton::arch::x86::ID_INS_VFMADDSD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADD213SD:
            tritonId = triton::arch::x86::ID_INS_VFMADD213SD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADD132SD:
            tritonId = triton::arch::x86::ID_INS_VFMADD132SD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADD231SD:
            tritonId = triton::arch::x86::ID_INS_VFMADD231SD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADDSS:
            tritonId = triton::arch::x86::ID_INS_VFMADDSS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADD213SS:
            tritonId = triton::arch::x86::ID_INS_VFMADD213SS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADD132SS:
            tritonId = triton::arch::x86::ID_INS_VFMADD132SS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADD231SS:
            tritonId = triton::arch::x86::ID_INS_VFMADD231SS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADDSUB132PD:
            tritonId = triton::arch::x86::ID_INS_VFMADDSUB132PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADDSUB132PS:
            tritonId = triton::arch::x86::ID_INS_VFMADDSUB132PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADDSUB213PD:
            tritonId = triton::arch::x86::ID_INS_VFMADDSUB213PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADDSUB213PS:
            tritonId = triton::arch::x86::ID_INS_VFMADDSUB213PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADDSUBPD:
            tritonId = triton::arch::x86::ID_INS_VFMADDSUBPD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADDSUB231PD:
            tritonId = triton::arch::x86::ID_INS_VFMADDSUB231PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADDSUBPS:
            tritonId = triton::arch::x86::ID_INS_VFMADDSUBPS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMADDSUB231PS:
            tritonId = triton::arch::x86::ID_INS_VFMADDSUB231PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUB132PD:
            tritonId = triton::arch::x86::ID_INS_VFMSUB132PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUB132PS:
            tritonId = triton::arch::x86::ID_INS_VFMSUB132PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUB213PD:
            tritonId = triton::arch::x86::ID_INS_VFMSUB213PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUB213PS:
            tritonId = triton::arch::x86::ID_INS_VFMSUB213PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUBADD132PD:
            tritonId = triton::arch::x86::ID_INS_VFMSUBADD132PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUBADD132PS:
            tritonId = triton::arch::x86::ID_INS_VFMSUBADD132PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUBADD213PD:
            tritonId = triton::arch::x86::ID_INS_VFMSUBADD213PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUBADD213PS:
            tritonId = triton::arch::x86::ID_INS_VFMSUBADD213PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUBADDPD:
            tritonId = triton::arch::x86::ID_INS_VFMSUBADDPD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUBADD231PD:
            tritonId = triton::arch::x86::ID_INS_VFMSUBADD231PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUBADDPS:
            tritonId = triton::arch::x86::ID_INS_VFMSUBADDPS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUBADD231PS:
            tritonId = triton::arch::x86::ID_INS_VFMSUBADD231PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUBPD:
            tritonId = triton::arch::x86::ID_INS_VFMSUBPD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUB231PD:
            tritonId = triton::arch::x86::ID_INS_VFMSUB231PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUBPS:
            tritonId = triton::arch::x86::ID_INS_VFMSUBPS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUB231PS:
            tritonId = triton::arch::x86::ID_INS_VFMSUB231PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUBSD:
            tritonId = triton::arch::x86::ID_INS_VFMSUBSD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUB213SD:
            tritonId = triton::arch::x86::ID_INS_VFMSUB213SD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUB132SD:
            tritonId = triton::arch::x86::ID_INS_VFMSUB132SD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUB231SD:
            tritonId = triton::arch::x86::ID_INS_VFMSUB231SD;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUBSS:
            tritonId = triton::arch::x86::ID_INS_VFMSUBSS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUB213SS:
            tritonId = triton::arch::x86::ID_INS_VFMSUB213SS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUB132SS:
            tritonId = triton::arch::x86::ID_INS_VFMSUB132SS;
            break;

          case triton::extlibs::capstone::X86_INS_VFMSUB231SS:
            tritonId = triton::arch::x86::ID_INS_VFMSUB231SS;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMADD132PD:
            tritonId = triton::arch::x86::ID_INS_VFNMADD132PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMADD132PS:
            tritonId = triton::arch::x86::ID_INS_VFNMADD132PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMADD213PD:
            tritonId = triton::arch::x86::ID_INS_VFNMADD213PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMADD213PS:
            tritonId = triton::arch::x86::ID_INS_VFNMADD213PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMADDPD:
            tritonId = triton::arch::x86::ID_INS_VFNMADDPD;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMADD231PD:
            tritonId = triton::arch::x86::ID_INS_VFNMADD231PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMADDPS:
            tritonId = triton::arch::x86::ID_INS_VFNMADDPS;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMADD231PS:
            tritonId = triton::arch::x86::ID_INS_VFNMADD231PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMADDSD:
            tritonId = triton::arch::x86::ID_INS_VFNMADDSD;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMADD213SD:
            tritonId = triton::arch::x86::ID_INS_VFNMADD213SD;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMADD132SD:
            tritonId = triton::arch::x86::ID_INS_VFNMADD132SD;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMADD231SD:
            tritonId = triton::arch::x86::ID_INS_VFNMADD231SD;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMADDSS:
            tritonId = triton::arch::x86::ID_INS_VFNMADDSS;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMADD213SS:
            tritonId = triton::arch::x86::ID_INS_VFNMADD213SS;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMADD132SS:
            tritonId = triton::arch::x86::ID_INS_VFNMADD132SS;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMADD231SS:
            tritonId = triton::arch::x86::ID_INS_VFNMADD231SS;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMSUB132PD:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB132PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMSUB132PS:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB132PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMSUB213PD:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB213PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMSUB213PS:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB213PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMSUBPD:
            tritonId = triton::arch::x86::ID_INS_VFNMSUBPD;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMSUB231PD:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB231PD;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMSUBPS:
            tritonId = triton::arch::x86::ID_INS_VFNMSUBPS;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMSUB231PS:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB231PS;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMSUBSD:
            tritonId = triton::arch::x86::ID_INS_VFNMSUBSD;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMSUB213SD:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB213SD;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMSUB132SD:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB132SD;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMSUB231SD:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB231SD;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMSUBSS:
            tritonId = triton::arch::x86::ID_INS_VFNMSUBSS;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMSUB213SS:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB213SS;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMSUB132SS:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB132SS;
            break;

          case triton::extlibs::capstone::X86_INS_VFNMSUB231SS:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB231SS;
            break;

          case triton::extlibs::capstone::X86_INS_VFRCZPD:
            tritonId = triton::arch::x86::ID_INS_VFRCZPD;
            break;

          case triton::extlibs::capstone::X86_INS_VFRCZPS:
            tritonId = triton::arch::x86::ID_INS_VFRCZPS;
            break;

          case triton::extlibs::capstone::X86_INS_VFRCZSD:
            tritonId = triton::arch::x86::ID_INS_VFRCZSD;
            break;

          case triton::extlibs::capstone::X86_INS_VFRCZSS:
            tritonId = triton::arch::x86::ID_INS_VFRCZSS;
            break;

          case triton::extlibs::capstone::X86_INS_VORPD:
            tritonId = triton::arch::x86::ID_INS_VORPD;
            break;

          case triton::extlibs::capstone::X86_INS_VORPS:
            tritonId = triton::arch::x86::ID_INS_VORPS;
            break;

          case triton::extlibs::capstone::X86_INS_VXORPD:
            tritonId = triton::arch::x86::ID_INS_VXORPD;
            break;

          case triton::extlibs::capstone::X86_INS_VXORPS:
            tritonId = triton::arch::x86::ID_INS_VXORPS;
            break;

          case triton::extlibs::capstone::X86_INS_VGATHERDPD:
            tritonId = triton::arch::x86::ID_INS_VGATHERDPD;
            break;

          case triton::extlibs::capstone::X86_INS_VGATHERDPS:
            tritonId = triton::arch::x86::ID_INS_VGATHERDPS;
            break;

          case triton::extlibs::capstone::X86_INS_VGATHERPF0DPD:
            tritonId = triton::arch::x86::ID_INS_VGATHERPF0DPD;
            break;

          case triton::extlibs::capstone::X86_INS_VGATHERPF0DPS:
            tritonId = triton::arch::x86::ID_INS_VGATHERPF0DPS;
            break;

          case triton::extlibs::capstone::X86_INS_VGATHERPF0QPD:
            tritonId = triton::arch::x86::ID_INS_VGATHERPF0QPD;
            break;

          case triton::extlibs::capstone::X86_INS_VGATHERPF0QPS:
            tritonId = triton::arch::x86::ID_INS_VGATHERPF0QPS;
            break;

          case triton::extlibs::capstone::X86_INS_VGATHERPF1DPD:
            tritonId = triton::arch::x86::ID_INS_VGATHERPF1DPD;
            break;

          case triton::extlibs::capstone::X86_INS_VGATHERPF1DPS:
            tritonId = triton::arch::x86::ID_INS_VGATHERPF1DPS;
            break;

          case triton::extlibs::capstone::X86_INS_VGATHERPF1QPD:
            tritonId = triton::arch::x86::ID_INS_VGATHERPF1QPD;
            break;

          case triton::extlibs::capstone::X86_INS_VGATHERPF1QPS:
            tritonId = triton::arch::x86::ID_INS_VGATHERPF1QPS;
            break;

          case triton::extlibs::capstone::X86_INS_VGATHERQPD:
            tritonId = triton::arch::x86::ID_INS_VGATHERQPD;
            break;

          case triton::extlibs::capstone::X86_INS_VGATHERQPS:
            tritonId = triton::arch::x86::ID_INS_VGATHERQPS;
            break;

          case triton::extlibs::capstone::X86_INS_VHADDPD:
            tritonId = triton::arch::x86::ID_INS_VHADDPD;
            break;

          case triton::extlibs::capstone::X86_INS_VHADDPS:
            tritonId = triton::arch::x86::ID_INS_VHADDPS;
            break;

          case triton::extlibs::capstone::X86_INS_VHSUBPD:
            tritonId = triton::arch::x86::ID_INS_VHSUBPD;
            break;

          case triton::extlibs::capstone::X86_INS_VHSUBPS:
            tritonId = triton::arch::x86::ID_INS_VHSUBPS;
            break;

          case triton::extlibs::capstone::X86_INS_VINSERTF128:
            tritonId = triton::arch::x86::ID_INS_VINSERTF128;
            break;

          case triton::extlibs::capstone::X86_INS_VINSERTF32X4:
            tritonId = triton::arch::x86::ID_INS_VINSERTF32X4;
            break;

          case triton::extlibs::capstone::X86_INS_VINSERTF64X4:
            tritonId = triton::arch::x86::ID_INS_VINSERTF64X4;
            break;

          case triton::extlibs::capstone::X86_INS_VINSERTI128:
            tritonId = triton::arch::x86::ID_INS_VINSERTI128;
            break;

          case triton::extlibs::capstone::X86_INS_VINSERTI32X4:
            tritonId = triton::arch::x86::ID_INS_VINSERTI32X4;
            break;

          case triton::extlibs::capstone::X86_INS_VINSERTI64X4:
            tritonId = triton::arch::x86::ID_INS_VINSERTI64X4;
            break;

          case triton::extlibs::capstone::X86_INS_VINSERTPS:
            tritonId = triton::arch::x86::ID_INS_VINSERTPS;
            break;

          case triton::extlibs::capstone::X86_INS_VLDDQU:
            tritonId = triton::arch::x86::ID_INS_VLDDQU;
            break;

          case triton::extlibs::capstone::X86_INS_VLDMXCSR:
            tritonId = triton::arch::x86::ID_INS_VLDMXCSR;
            break;

          case triton::extlibs::capstone::X86_INS_VMASKMOVDQU:
            tritonId = triton::arch::x86::ID_INS_VMASKMOVDQU;
            break;

          case triton::extlibs::capstone::X86_INS_VMASKMOVPD:
            tritonId = triton::arch::x86::ID_INS_VMASKMOVPD;
            break;

          case triton::extlibs::capstone::X86_INS_VMASKMOVPS:
            tritonId = triton::arch::x86::ID_INS_VMASKMOVPS;
            break;

          case triton::extlibs::capstone::X86_INS_VMAXPD:
            tritonId = triton::arch::x86::ID_INS_VMAXPD;
            break;

          case triton::extlibs::capstone::X86_INS_VMAXPS:
            tritonId = triton::arch::x86::ID_INS_VMAXPS;
            break;

          case triton::extlibs::capstone::X86_INS_VMAXSD:
            tritonId = triton::arch::x86::ID_INS_VMAXSD;
            break;

          case triton::extlibs::capstone::X86_INS_VMAXSS:
            tritonId = triton::arch::x86::ID_INS_VMAXSS;
            break;

          case triton::extlibs::capstone::X86_INS_VMCALL:
            tritonId = triton::arch::x86::ID_INS_VMCALL;
            break;

          case triton::extlibs::capstone::X86_INS_VMCLEAR:
            tritonId = triton::arch::x86::ID_INS_VMCLEAR;
            break;

          case triton::extlibs::capstone::X86_INS_VMFUNC:
            tritonId = triton::arch::x86::ID_INS_VMFUNC;
            break;

          case triton::extlibs::capstone::X86_INS_VMINPD:
            tritonId = triton::arch::x86::ID_INS_VMINPD;
            break;

          case triton::extlibs::capstone::X86_INS_VMINPS:
            tritonId = triton::arch::x86::ID_INS_VMINPS;
            break;

          case triton::extlibs::capstone::X86_INS_VMINSD:
            tritonId = triton::arch::x86::ID_INS_VMINSD;
            break;

          case triton::extlibs::capstone::X86_INS_VMINSS:
            tritonId = triton::arch::x86::ID_INS_VMINSS;
            break;

          case triton::extlibs::capstone::X86_INS_VMLAUNCH:
            tritonId = triton::arch::x86::ID_INS_VMLAUNCH;
            break;

          case triton::extlibs::capstone::X86_INS_VMLOAD:
            tritonId = triton::arch::x86::ID_INS_VMLOAD;
            break;

          case triton::extlibs::capstone::X86_INS_VMMCALL:
            tritonId = triton::arch::x86::ID_INS_VMMCALL;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVQ:
            tritonId = triton::arch::x86::ID_INS_VMOVQ;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVDDUP:
            tritonId = triton::arch::x86::ID_INS_VMOVDDUP;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVD:
            tritonId = triton::arch::x86::ID_INS_VMOVD;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVDQA32:
            tritonId = triton::arch::x86::ID_INS_VMOVDQA32;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVDQA64:
            tritonId = triton::arch::x86::ID_INS_VMOVDQA64;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVDQA:
            tritonId = triton::arch::x86::ID_INS_VMOVDQA;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVDQU16:
            tritonId = triton::arch::x86::ID_INS_VMOVDQU16;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVDQU32:
            tritonId = triton::arch::x86::ID_INS_VMOVDQU32;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVDQU64:
            tritonId = triton::arch::x86::ID_INS_VMOVDQU64;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVDQU8:
            tritonId = triton::arch::x86::ID_INS_VMOVDQU8;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVDQU:
            tritonId = triton::arch::x86::ID_INS_VMOVDQU;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVHLPS:
            tritonId = triton::arch::x86::ID_INS_VMOVHLPS;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVHPD:
            tritonId = triton::arch::x86::ID_INS_VMOVHPD;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVHPS:
            tritonId = triton::arch::x86::ID_INS_VMOVHPS;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVLHPS:
            tritonId = triton::arch::x86::ID_INS_VMOVLHPS;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVLPD:
            tritonId = triton::arch::x86::ID_INS_VMOVLPD;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVLPS:
            tritonId = triton::arch::x86::ID_INS_VMOVLPS;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVMSKPD:
            tritonId = triton::arch::x86::ID_INS_VMOVMSKPD;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVMSKPS:
            tritonId = triton::arch::x86::ID_INS_VMOVMSKPS;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVNTDQA:
            tritonId = triton::arch::x86::ID_INS_VMOVNTDQA;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVNTDQ:
            tritonId = triton::arch::x86::ID_INS_VMOVNTDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVNTPD:
            tritonId = triton::arch::x86::ID_INS_VMOVNTPD;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVNTPS:
            tritonId = triton::arch::x86::ID_INS_VMOVNTPS;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVSD:
            tritonId = triton::arch::x86::ID_INS_VMOVSD;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVSHDUP:
            tritonId = triton::arch::x86::ID_INS_VMOVSHDUP;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVSLDUP:
            tritonId = triton::arch::x86::ID_INS_VMOVSLDUP;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVSS:
            tritonId = triton::arch::x86::ID_INS_VMOVSS;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVUPD:
            tritonId = triton::arch::x86::ID_INS_VMOVUPD;
            break;

          case triton::extlibs::capstone::X86_INS_VMOVUPS:
            tritonId = triton::arch::x86::ID_INS_VMOVUPS;
            break;

          case triton::extlibs::capstone::X86_INS_VMPSADBW:
            tritonId = triton::arch::x86::ID_INS_VMPSADBW;
            break;

          case triton::extlibs::capstone::X86_INS_VMPTRLD:
            tritonId = triton::arch::x86::ID_INS_VMPTRLD;
            break;

          case triton::extlibs::capstone::X86_INS_VMPTRST:
            tritonId = triton::arch::x86::ID_INS_VMPTRST;
            break;

          case triton::extlibs::capstone::X86_INS_VMREAD:
            tritonId = triton::arch::x86::ID_INS_VMREAD;
            break;

          case triton::extlibs::capstone::X86_INS_VMRESUME:
            tritonId = triton::arch::x86::ID_INS_VMRESUME;
            break;

          case triton::extlibs::capstone::X86_INS_VMRUN:
            tritonId = triton::arch::x86::ID_INS_VMRUN;
            break;

          case triton::extlibs::capstone::X86_INS_VMSAVE:
            tritonId = triton::arch::x86::ID_INS_VMSAVE;
            break;

          case triton::extlibs::capstone::X86_INS_VMULPD:
            tritonId = triton::arch::x86::ID_INS_VMULPD;
            break;

          case triton::extlibs::capstone::X86_INS_VMULPS:
            tritonId = triton::arch::x86::ID_INS_VMULPS;
            break;

          case triton::extlibs::capstone::X86_INS_VMULSD:
            tritonId = triton::arch::x86::ID_INS_VMULSD;
            break;

          case triton::extlibs::capstone::X86_INS_VMULSS:
            tritonId = triton::arch::x86::ID_INS_VMULSS;
            break;

          case triton::extlibs::capstone::X86_INS_VMWRITE:
            tritonId = triton::arch::x86::ID_INS_VMWRITE;
            break;

          case triton::extlibs::capstone::X86_INS_VMXOFF:
            tritonId = triton::arch::x86::ID_INS_VMXOFF;
            break;

          case triton::extlibs::capstone::X86_INS_VMXON:
            tritonId = triton::arch::x86::ID_INS_VMXON;
            break;

          case triton::extlibs::capstone::X86_INS_VPABSB:
            tritonId = triton::arch::x86::ID_INS_VPABSB;
            break;

          case triton::extlibs::capstone::X86_INS_VPABSD:
            tritonId = triton::arch::x86::ID_INS_VPABSD;
            break;

          case triton::extlibs::capstone::X86_INS_VPABSQ:
            tritonId = triton::arch::x86::ID_INS_VPABSQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPABSW:
            tritonId = triton::arch::x86::ID_INS_VPABSW;
            break;

          case triton::extlibs::capstone::X86_INS_VPACKSSDW:
            tritonId = triton::arch::x86::ID_INS_VPACKSSDW;
            break;

          case triton::extlibs::capstone::X86_INS_VPACKSSWB:
            tritonId = triton::arch::x86::ID_INS_VPACKSSWB;
            break;

          case triton::extlibs::capstone::X86_INS_VPACKUSDW:
            tritonId = triton::arch::x86::ID_INS_VPACKUSDW;
            break;

          case triton::extlibs::capstone::X86_INS_VPACKUSWB:
            tritonId = triton::arch::x86::ID_INS_VPACKUSWB;
            break;

          case triton::extlibs::capstone::X86_INS_VPADDB:
            tritonId = triton::arch::x86::ID_INS_VPADDB;
            break;

          case triton::extlibs::capstone::X86_INS_VPADDD:
            tritonId = triton::arch::x86::ID_INS_VPADDD;
            break;

          case triton::extlibs::capstone::X86_INS_VPADDQ:
            tritonId = triton::arch::x86::ID_INS_VPADDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPADDSB:
            tritonId = triton::arch::x86::ID_INS_VPADDSB;
            break;

          case triton::extlibs::capstone::X86_INS_VPADDSW:
            tritonId = triton::arch::x86::ID_INS_VPADDSW;
            break;

          case triton::extlibs::capstone::X86_INS_VPADDUSB:
            tritonId = triton::arch::x86::ID_INS_VPADDUSB;
            break;

          case triton::extlibs::capstone::X86_INS_VPADDUSW:
            tritonId = triton::arch::x86::ID_INS_VPADDUSW;
            break;

          case triton::extlibs::capstone::X86_INS_VPADDW:
            tritonId = triton::arch::x86::ID_INS_VPADDW;
            break;

          case triton::extlibs::capstone::X86_INS_VPALIGNR:
            tritonId = triton::arch::x86::ID_INS_VPALIGNR;
            break;

          case triton::extlibs::capstone::X86_INS_VPANDD:
            tritonId = triton::arch::x86::ID_INS_VPANDD;
            break;

          case triton::extlibs::capstone::X86_INS_VPANDND:
            tritonId = triton::arch::x86::ID_INS_VPANDND;
            break;

          case triton::extlibs::capstone::X86_INS_VPANDNQ:
            tritonId = triton::arch::x86::ID_INS_VPANDNQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPANDN:
            tritonId = triton::arch::x86::ID_INS_VPANDN;
            break;

          case triton::extlibs::capstone::X86_INS_VPANDQ:
            tritonId = triton::arch::x86::ID_INS_VPANDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPAND:
            tritonId = triton::arch::x86::ID_INS_VPAND;
            break;

          case triton::extlibs::capstone::X86_INS_VPAVGB:
            tritonId = triton::arch::x86::ID_INS_VPAVGB;
            break;

          case triton::extlibs::capstone::X86_INS_VPAVGW:
            tritonId = triton::arch::x86::ID_INS_VPAVGW;
            break;

          case triton::extlibs::capstone::X86_INS_VPBLENDD:
            tritonId = triton::arch::x86::ID_INS_VPBLENDD;
            break;

          case triton::extlibs::capstone::X86_INS_VPBLENDMD:
            tritonId = triton::arch::x86::ID_INS_VPBLENDMD;
            break;

          case triton::extlibs::capstone::X86_INS_VPBLENDMQ:
            tritonId = triton::arch::x86::ID_INS_VPBLENDMQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPBLENDVB:
            tritonId = triton::arch::x86::ID_INS_VPBLENDVB;
            break;

          case triton::extlibs::capstone::X86_INS_VPBLENDW:
            tritonId = triton::arch::x86::ID_INS_VPBLENDW;
            break;

          case triton::extlibs::capstone::X86_INS_VPBROADCASTB:
            tritonId = triton::arch::x86::ID_INS_VPBROADCASTB;
            break;

          case triton::extlibs::capstone::X86_INS_VPBROADCASTD:
            tritonId = triton::arch::x86::ID_INS_VPBROADCASTD;
            break;

          case triton::extlibs::capstone::X86_INS_VPBROADCASTMB2Q:
            tritonId = triton::arch::x86::ID_INS_VPBROADCASTMB2Q;
            break;

          case triton::extlibs::capstone::X86_INS_VPBROADCASTMW2D:
            tritonId = triton::arch::x86::ID_INS_VPBROADCASTMW2D;
            break;

          case triton::extlibs::capstone::X86_INS_VPBROADCASTQ:
            tritonId = triton::arch::x86::ID_INS_VPBROADCASTQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPBROADCASTW:
            tritonId = triton::arch::x86::ID_INS_VPBROADCASTW;
            break;

          case triton::extlibs::capstone::X86_INS_VPCLMULQDQ:
            tritonId = triton::arch::x86::ID_INS_VPCLMULQDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMOV:
            tritonId = triton::arch::x86::ID_INS_VPCMOV;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMP:
            tritonId = triton::arch::x86::ID_INS_VPCMP;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMPD:
            tritonId = triton::arch::x86::ID_INS_VPCMPD;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMPEQB:
            tritonId = triton::arch::x86::ID_INS_VPCMPEQB;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMPEQD:
            tritonId = triton::arch::x86::ID_INS_VPCMPEQD;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMPEQQ:
            tritonId = triton::arch::x86::ID_INS_VPCMPEQQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMPEQW:
            tritonId = triton::arch::x86::ID_INS_VPCMPEQW;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMPESTRI:
            tritonId = triton::arch::x86::ID_INS_VPCMPESTRI;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMPESTRM:
            tritonId = triton::arch::x86::ID_INS_VPCMPESTRM;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMPGTB:
            tritonId = triton::arch::x86::ID_INS_VPCMPGTB;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMPGTD:
            tritonId = triton::arch::x86::ID_INS_VPCMPGTD;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMPGTQ:
            tritonId = triton::arch::x86::ID_INS_VPCMPGTQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMPGTW:
            tritonId = triton::arch::x86::ID_INS_VPCMPGTW;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMPISTRI:
            tritonId = triton::arch::x86::ID_INS_VPCMPISTRI;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMPISTRM:
            tritonId = triton::arch::x86::ID_INS_VPCMPISTRM;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMPQ:
            tritonId = triton::arch::x86::ID_INS_VPCMPQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMPUD:
            tritonId = triton::arch::x86::ID_INS_VPCMPUD;
            break;

          case triton::extlibs::capstone::X86_INS_VPCMPUQ:
            tritonId = triton::arch::x86::ID_INS_VPCMPUQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPCOMB:
            tritonId = triton::arch::x86::ID_INS_VPCOMB;
            break;

          case triton::extlibs::capstone::X86_INS_VPCOMD:
            tritonId = triton::arch::x86::ID_INS_VPCOMD;
            break;

          case triton::extlibs::capstone::X86_INS_VPCOMQ:
            tritonId = triton::arch::x86::ID_INS_VPCOMQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPCOMUB:
            tritonId = triton::arch::x86::ID_INS_VPCOMUB;
            break;

          case triton::extlibs::capstone::X86_INS_VPCOMUD:
            tritonId = triton::arch::x86::ID_INS_VPCOMUD;
            break;

          case triton::extlibs::capstone::X86_INS_VPCOMUQ:
            tritonId = triton::arch::x86::ID_INS_VPCOMUQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPCOMUW:
            tritonId = triton::arch::x86::ID_INS_VPCOMUW;
            break;

          case triton::extlibs::capstone::X86_INS_VPCOMW:
            tritonId = triton::arch::x86::ID_INS_VPCOMW;
            break;

          case triton::extlibs::capstone::X86_INS_VPCONFLICTD:
            tritonId = triton::arch::x86::ID_INS_VPCONFLICTD;
            break;

          case triton::extlibs::capstone::X86_INS_VPCONFLICTQ:
            tritonId = triton::arch::x86::ID_INS_VPCONFLICTQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPERM2F128:
            tritonId = triton::arch::x86::ID_INS_VPERM2F128;
            break;

          case triton::extlibs::capstone::X86_INS_VPERM2I128:
            tritonId = triton::arch::x86::ID_INS_VPERM2I128;
            break;

          case triton::extlibs::capstone::X86_INS_VPERMD:
            tritonId = triton::arch::x86::ID_INS_VPERMD;
            break;

          case triton::extlibs::capstone::X86_INS_VPERMI2D:
            tritonId = triton::arch::x86::ID_INS_VPERMI2D;
            break;

          case triton::extlibs::capstone::X86_INS_VPERMI2PD:
            tritonId = triton::arch::x86::ID_INS_VPERMI2PD;
            break;

          case triton::extlibs::capstone::X86_INS_VPERMI2PS:
            tritonId = triton::arch::x86::ID_INS_VPERMI2PS;
            break;

          case triton::extlibs::capstone::X86_INS_VPERMI2Q:
            tritonId = triton::arch::x86::ID_INS_VPERMI2Q;
            break;

          case triton::extlibs::capstone::X86_INS_VPERMIL2PD:
            tritonId = triton::arch::x86::ID_INS_VPERMIL2PD;
            break;

          case triton::extlibs::capstone::X86_INS_VPERMIL2PS:
            tritonId = triton::arch::x86::ID_INS_VPERMIL2PS;
            break;

          case triton::extlibs::capstone::X86_INS_VPERMILPD:
            tritonId = triton::arch::x86::ID_INS_VPERMILPD;
            break;

          case triton::extlibs::capstone::X86_INS_VPERMILPS:
            tritonId = triton::arch::x86::ID_INS_VPERMILPS;
            break;

          case triton::extlibs::capstone::X86_INS_VPERMPD:
            tritonId = triton::arch::x86::ID_INS_VPERMPD;
            break;

          case triton::extlibs::capstone::X86_INS_VPERMPS:
            tritonId = triton::arch::x86::ID_INS_VPERMPS;
            break;

          case triton::extlibs::capstone::X86_INS_VPERMQ:
            tritonId = triton::arch::x86::ID_INS_VPERMQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPERMT2D:
            tritonId = triton::arch::x86::ID_INS_VPERMT2D;
            break;

          case triton::extlibs::capstone::X86_INS_VPERMT2PD:
            tritonId = triton::arch::x86::ID_INS_VPERMT2PD;
            break;

          case triton::extlibs::capstone::X86_INS_VPERMT2PS:
            tritonId = triton::arch::x86::ID_INS_VPERMT2PS;
            break;

          case triton::extlibs::capstone::X86_INS_VPERMT2Q:
            tritonId = triton::arch::x86::ID_INS_VPERMT2Q;
            break;

          case triton::extlibs::capstone::X86_INS_VPEXTRB:
            tritonId = triton::arch::x86::ID_INS_VPEXTRB;
            break;

          case triton::extlibs::capstone::X86_INS_VPEXTRD:
            tritonId = triton::arch::x86::ID_INS_VPEXTRD;
            break;

          case triton::extlibs::capstone::X86_INS_VPEXTRQ:
            tritonId = triton::arch::x86::ID_INS_VPEXTRQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPEXTRW:
            tritonId = triton::arch::x86::ID_INS_VPEXTRW;
            break;

          case triton::extlibs::capstone::X86_INS_VPGATHERDD:
            tritonId = triton::arch::x86::ID_INS_VPGATHERDD;
            break;

          case triton::extlibs::capstone::X86_INS_VPGATHERDQ:
            tritonId = triton::arch::x86::ID_INS_VPGATHERDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPGATHERQD:
            tritonId = triton::arch::x86::ID_INS_VPGATHERQD;
            break;

          case triton::extlibs::capstone::X86_INS_VPGATHERQQ:
            tritonId = triton::arch::x86::ID_INS_VPGATHERQQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPHADDBD:
            tritonId = triton::arch::x86::ID_INS_VPHADDBD;
            break;

          case triton::extlibs::capstone::X86_INS_VPHADDBQ:
            tritonId = triton::arch::x86::ID_INS_VPHADDBQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPHADDBW:
            tritonId = triton::arch::x86::ID_INS_VPHADDBW;
            break;

          case triton::extlibs::capstone::X86_INS_VPHADDDQ:
            tritonId = triton::arch::x86::ID_INS_VPHADDDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPHADDD:
            tritonId = triton::arch::x86::ID_INS_VPHADDD;
            break;

          case triton::extlibs::capstone::X86_INS_VPHADDSW:
            tritonId = triton::arch::x86::ID_INS_VPHADDSW;
            break;

          case triton::extlibs::capstone::X86_INS_VPHADDUBD:
            tritonId = triton::arch::x86::ID_INS_VPHADDUBD;
            break;

          case triton::extlibs::capstone::X86_INS_VPHADDUBQ:
            tritonId = triton::arch::x86::ID_INS_VPHADDUBQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPHADDUBW:
            tritonId = triton::arch::x86::ID_INS_VPHADDUBW;
            break;

          case triton::extlibs::capstone::X86_INS_VPHADDUDQ:
            tritonId = triton::arch::x86::ID_INS_VPHADDUDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPHADDUWD:
            tritonId = triton::arch::x86::ID_INS_VPHADDUWD;
            break;

          case triton::extlibs::capstone::X86_INS_VPHADDUWQ:
            tritonId = triton::arch::x86::ID_INS_VPHADDUWQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPHADDWD:
            tritonId = triton::arch::x86::ID_INS_VPHADDWD;
            break;

          case triton::extlibs::capstone::X86_INS_VPHADDWQ:
            tritonId = triton::arch::x86::ID_INS_VPHADDWQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPHADDW:
            tritonId = triton::arch::x86::ID_INS_VPHADDW;
            break;

          case triton::extlibs::capstone::X86_INS_VPHMINPOSUW:
            tritonId = triton::arch::x86::ID_INS_VPHMINPOSUW;
            break;

          case triton::extlibs::capstone::X86_INS_VPHSUBBW:
            tritonId = triton::arch::x86::ID_INS_VPHSUBBW;
            break;

          case triton::extlibs::capstone::X86_INS_VPHSUBDQ:
            tritonId = triton::arch::x86::ID_INS_VPHSUBDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPHSUBD:
            tritonId = triton::arch::x86::ID_INS_VPHSUBD;
            break;

          case triton::extlibs::capstone::X86_INS_VPHSUBSW:
            tritonId = triton::arch::x86::ID_INS_VPHSUBSW;
            break;

          case triton::extlibs::capstone::X86_INS_VPHSUBWD:
            tritonId = triton::arch::x86::ID_INS_VPHSUBWD;
            break;

          case triton::extlibs::capstone::X86_INS_VPHSUBW:
            tritonId = triton::arch::x86::ID_INS_VPHSUBW;
            break;

          case triton::extlibs::capstone::X86_INS_VPINSRB:
            tritonId = triton::arch::x86::ID_INS_VPINSRB;
            break;

          case triton::extlibs::capstone::X86_INS_VPINSRD:
            tritonId = triton::arch::x86::ID_INS_VPINSRD;
            break;

          case triton::extlibs::capstone::X86_INS_VPINSRQ:
            tritonId = triton::arch::x86::ID_INS_VPINSRQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPINSRW:
            tritonId = triton::arch::x86::ID_INS_VPINSRW;
            break;

          case triton::extlibs::capstone::X86_INS_VPLZCNTD:
            tritonId = triton::arch::x86::ID_INS_VPLZCNTD;
            break;

          case triton::extlibs::capstone::X86_INS_VPLZCNTQ:
            tritonId = triton::arch::x86::ID_INS_VPLZCNTQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPMACSDD:
            tritonId = triton::arch::x86::ID_INS_VPMACSDD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMACSDQH:
            tritonId = triton::arch::x86::ID_INS_VPMACSDQH;
            break;

          case triton::extlibs::capstone::X86_INS_VPMACSDQL:
            tritonId = triton::arch::x86::ID_INS_VPMACSDQL;
            break;

          case triton::extlibs::capstone::X86_INS_VPMACSSDD:
            tritonId = triton::arch::x86::ID_INS_VPMACSSDD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMACSSDQH:
            tritonId = triton::arch::x86::ID_INS_VPMACSSDQH;
            break;

          case triton::extlibs::capstone::X86_INS_VPMACSSDQL:
            tritonId = triton::arch::x86::ID_INS_VPMACSSDQL;
            break;

          case triton::extlibs::capstone::X86_INS_VPMACSSWD:
            tritonId = triton::arch::x86::ID_INS_VPMACSSWD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMACSSWW:
            tritonId = triton::arch::x86::ID_INS_VPMACSSWW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMACSWD:
            tritonId = triton::arch::x86::ID_INS_VPMACSWD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMACSWW:
            tritonId = triton::arch::x86::ID_INS_VPMACSWW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMADCSSWD:
            tritonId = triton::arch::x86::ID_INS_VPMADCSSWD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMADCSWD:
            tritonId = triton::arch::x86::ID_INS_VPMADCSWD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMADDUBSW:
            tritonId = triton::arch::x86::ID_INS_VPMADDUBSW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMADDWD:
            tritonId = triton::arch::x86::ID_INS_VPMADDWD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMASKMOVD:
            tritonId = triton::arch::x86::ID_INS_VPMASKMOVD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMASKMOVQ:
            tritonId = triton::arch::x86::ID_INS_VPMASKMOVQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPMAXSB:
            tritonId = triton::arch::x86::ID_INS_VPMAXSB;
            break;

          case triton::extlibs::capstone::X86_INS_VPMAXSD:
            tritonId = triton::arch::x86::ID_INS_VPMAXSD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMAXSQ:
            tritonId = triton::arch::x86::ID_INS_VPMAXSQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPMAXSW:
            tritonId = triton::arch::x86::ID_INS_VPMAXSW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMAXUB:
            tritonId = triton::arch::x86::ID_INS_VPMAXUB;
            break;

          case triton::extlibs::capstone::X86_INS_VPMAXUD:
            tritonId = triton::arch::x86::ID_INS_VPMAXUD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMAXUQ:
            tritonId = triton::arch::x86::ID_INS_VPMAXUQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPMAXUW:
            tritonId = triton::arch::x86::ID_INS_VPMAXUW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMINSB:
            tritonId = triton::arch::x86::ID_INS_VPMINSB;
            break;

          case triton::extlibs::capstone::X86_INS_VPMINSD:
            tritonId = triton::arch::x86::ID_INS_VPMINSD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMINSQ:
            tritonId = triton::arch::x86::ID_INS_VPMINSQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPMINSW:
            tritonId = triton::arch::x86::ID_INS_VPMINSW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMINUB:
            tritonId = triton::arch::x86::ID_INS_VPMINUB;
            break;

          case triton::extlibs::capstone::X86_INS_VPMINUD:
            tritonId = triton::arch::x86::ID_INS_VPMINUD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMINUQ:
            tritonId = triton::arch::x86::ID_INS_VPMINUQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPMINUW:
            tritonId = triton::arch::x86::ID_INS_VPMINUW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVDB:
            tritonId = triton::arch::x86::ID_INS_VPMOVDB;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVDW:
            tritonId = triton::arch::x86::ID_INS_VPMOVDW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVMSKB:
            tritonId = triton::arch::x86::ID_INS_VPMOVMSKB;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVQB:
            tritonId = triton::arch::x86::ID_INS_VPMOVQB;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVQD:
            tritonId = triton::arch::x86::ID_INS_VPMOVQD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVQW:
            tritonId = triton::arch::x86::ID_INS_VPMOVQW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVSDB:
            tritonId = triton::arch::x86::ID_INS_VPMOVSDB;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVSDW:
            tritonId = triton::arch::x86::ID_INS_VPMOVSDW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVSQB:
            tritonId = triton::arch::x86::ID_INS_VPMOVSQB;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVSQD:
            tritonId = triton::arch::x86::ID_INS_VPMOVSQD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVSQW:
            tritonId = triton::arch::x86::ID_INS_VPMOVSQW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVSXBD:
            tritonId = triton::arch::x86::ID_INS_VPMOVSXBD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVSXBQ:
            tritonId = triton::arch::x86::ID_INS_VPMOVSXBQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVSXBW:
            tritonId = triton::arch::x86::ID_INS_VPMOVSXBW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVSXDQ:
            tritonId = triton::arch::x86::ID_INS_VPMOVSXDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVSXWD:
            tritonId = triton::arch::x86::ID_INS_VPMOVSXWD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVSXWQ:
            tritonId = triton::arch::x86::ID_INS_VPMOVSXWQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVUSDB:
            tritonId = triton::arch::x86::ID_INS_VPMOVUSDB;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVUSDW:
            tritonId = triton::arch::x86::ID_INS_VPMOVUSDW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVUSQB:
            tritonId = triton::arch::x86::ID_INS_VPMOVUSQB;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVUSQD:
            tritonId = triton::arch::x86::ID_INS_VPMOVUSQD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVUSQW:
            tritonId = triton::arch::x86::ID_INS_VPMOVUSQW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVZXBD:
            tritonId = triton::arch::x86::ID_INS_VPMOVZXBD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVZXBQ:
            tritonId = triton::arch::x86::ID_INS_VPMOVZXBQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVZXBW:
            tritonId = triton::arch::x86::ID_INS_VPMOVZXBW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVZXDQ:
            tritonId = triton::arch::x86::ID_INS_VPMOVZXDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVZXWD:
            tritonId = triton::arch::x86::ID_INS_VPMOVZXWD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMOVZXWQ:
            tritonId = triton::arch::x86::ID_INS_VPMOVZXWQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPMULDQ:
            tritonId = triton::arch::x86::ID_INS_VPMULDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPMULHRSW:
            tritonId = triton::arch::x86::ID_INS_VPMULHRSW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMULHUW:
            tritonId = triton::arch::x86::ID_INS_VPMULHUW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMULHW:
            tritonId = triton::arch::x86::ID_INS_VPMULHW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMULLD:
            tritonId = triton::arch::x86::ID_INS_VPMULLD;
            break;

          case triton::extlibs::capstone::X86_INS_VPMULLW:
            tritonId = triton::arch::x86::ID_INS_VPMULLW;
            break;

          case triton::extlibs::capstone::X86_INS_VPMULUDQ:
            tritonId = triton::arch::x86::ID_INS_VPMULUDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPORD:
            tritonId = triton::arch::x86::ID_INS_VPORD;
            break;

          case triton::extlibs::capstone::X86_INS_VPORQ:
            tritonId = triton::arch::x86::ID_INS_VPORQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPOR:
            tritonId = triton::arch::x86::ID_INS_VPOR;
            break;

          case triton::extlibs::capstone::X86_INS_VPPERM:
            tritonId = triton::arch::x86::ID_INS_VPPERM;
            break;

          case triton::extlibs::capstone::X86_INS_VPROTB:
            tritonId = triton::arch::x86::ID_INS_VPROTB;
            break;

          case triton::extlibs::capstone::X86_INS_VPROTD:
            tritonId = triton::arch::x86::ID_INS_VPROTD;
            break;

          case triton::extlibs::capstone::X86_INS_VPROTQ:
            tritonId = triton::arch::x86::ID_INS_VPROTQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPROTW:
            tritonId = triton::arch::x86::ID_INS_VPROTW;
            break;

          case triton::extlibs::capstone::X86_INS_VPSADBW:
            tritonId = triton::arch::x86::ID_INS_VPSADBW;
            break;

          case triton::extlibs::capstone::X86_INS_VPSCATTERDD:
            tritonId = triton::arch::x86::ID_INS_VPSCATTERDD;
            break;

          case triton::extlibs::capstone::X86_INS_VPSCATTERDQ:
            tritonId = triton::arch::x86::ID_INS_VPSCATTERDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPSCATTERQD:
            tritonId = triton::arch::x86::ID_INS_VPSCATTERQD;
            break;

          case triton::extlibs::capstone::X86_INS_VPSCATTERQQ:
            tritonId = triton::arch::x86::ID_INS_VPSCATTERQQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPSHAB:
            tritonId = triton::arch::x86::ID_INS_VPSHAB;
            break;

          case triton::extlibs::capstone::X86_INS_VPSHAD:
            tritonId = triton::arch::x86::ID_INS_VPSHAD;
            break;

          case triton::extlibs::capstone::X86_INS_VPSHAQ:
            tritonId = triton::arch::x86::ID_INS_VPSHAQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPSHAW:
            tritonId = triton::arch::x86::ID_INS_VPSHAW;
            break;

          case triton::extlibs::capstone::X86_INS_VPSHLB:
            tritonId = triton::arch::x86::ID_INS_VPSHLB;
            break;

          case triton::extlibs::capstone::X86_INS_VPSHLD:
            tritonId = triton::arch::x86::ID_INS_VPSHLD;
            break;

          case triton::extlibs::capstone::X86_INS_VPSHLQ:
            tritonId = triton::arch::x86::ID_INS_VPSHLQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPSHLW:
            tritonId = triton::arch::x86::ID_INS_VPSHLW;
            break;

          case triton::extlibs::capstone::X86_INS_VPSHUFB:
            tritonId = triton::arch::x86::ID_INS_VPSHUFB;
            break;

          case triton::extlibs::capstone::X86_INS_VPSHUFD:
            tritonId = triton::arch::x86::ID_INS_VPSHUFD;
            break;

          case triton::extlibs::capstone::X86_INS_VPSHUFHW:
            tritonId = triton::arch::x86::ID_INS_VPSHUFHW;
            break;

          case triton::extlibs::capstone::X86_INS_VPSHUFLW:
            tritonId = triton::arch::x86::ID_INS_VPSHUFLW;
            break;

          case triton::extlibs::capstone::X86_INS_VPSIGNB:
            tritonId = triton::arch::x86::ID_INS_VPSIGNB;
            break;

          case triton::extlibs::capstone::X86_INS_VPSIGND:
            tritonId = triton::arch::x86::ID_INS_VPSIGND;
            break;

          case triton::extlibs::capstone::X86_INS_VPSIGNW:
            tritonId = triton::arch::x86::ID_INS_VPSIGNW;
            break;

          case triton::extlibs::capstone::X86_INS_VPSLLDQ:
            tritonId = triton::arch::x86::ID_INS_VPSLLDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPSLLD:
            tritonId = triton::arch::x86::ID_INS_VPSLLD;
            break;

          case triton::extlibs::capstone::X86_INS_VPSLLQ:
            tritonId = triton::arch::x86::ID_INS_VPSLLQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPSLLVD:
            tritonId = triton::arch::x86::ID_INS_VPSLLVD;
            break;

          case triton::extlibs::capstone::X86_INS_VPSLLVQ:
            tritonId = triton::arch::x86::ID_INS_VPSLLVQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPSLLW:
            tritonId = triton::arch::x86::ID_INS_VPSLLW;
            break;

          case triton::extlibs::capstone::X86_INS_VPSRAD:
            tritonId = triton::arch::x86::ID_INS_VPSRAD;
            break;

          case triton::extlibs::capstone::X86_INS_VPSRAQ:
            tritonId = triton::arch::x86::ID_INS_VPSRAQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPSRAVD:
            tritonId = triton::arch::x86::ID_INS_VPSRAVD;
            break;

          case triton::extlibs::capstone::X86_INS_VPSRAVQ:
            tritonId = triton::arch::x86::ID_INS_VPSRAVQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPSRAW:
            tritonId = triton::arch::x86::ID_INS_VPSRAW;
            break;

          case triton::extlibs::capstone::X86_INS_VPSRLDQ:
            tritonId = triton::arch::x86::ID_INS_VPSRLDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPSRLD:
            tritonId = triton::arch::x86::ID_INS_VPSRLD;
            break;

          case triton::extlibs::capstone::X86_INS_VPSRLQ:
            tritonId = triton::arch::x86::ID_INS_VPSRLQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPSRLVD:
            tritonId = triton::arch::x86::ID_INS_VPSRLVD;
            break;

          case triton::extlibs::capstone::X86_INS_VPSRLVQ:
            tritonId = triton::arch::x86::ID_INS_VPSRLVQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPSRLW:
            tritonId = triton::arch::x86::ID_INS_VPSRLW;
            break;

          case triton::extlibs::capstone::X86_INS_VPSUBB:
            tritonId = triton::arch::x86::ID_INS_VPSUBB;
            break;

          case triton::extlibs::capstone::X86_INS_VPSUBD:
            tritonId = triton::arch::x86::ID_INS_VPSUBD;
            break;

          case triton::extlibs::capstone::X86_INS_VPSUBQ:
            tritonId = triton::arch::x86::ID_INS_VPSUBQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPSUBSB:
            tritonId = triton::arch::x86::ID_INS_VPSUBSB;
            break;

          case triton::extlibs::capstone::X86_INS_VPSUBSW:
            tritonId = triton::arch::x86::ID_INS_VPSUBSW;
            break;

          case triton::extlibs::capstone::X86_INS_VPSUBUSB:
            tritonId = triton::arch::x86::ID_INS_VPSUBUSB;
            break;

          case triton::extlibs::capstone::X86_INS_VPSUBUSW:
            tritonId = triton::arch::x86::ID_INS_VPSUBUSW;
            break;

          case triton::extlibs::capstone::X86_INS_VPSUBW:
            tritonId = triton::arch::x86::ID_INS_VPSUBW;
            break;

          case triton::extlibs::capstone::X86_INS_VPTESTMD:
            tritonId = triton::arch::x86::ID_INS_VPTESTMD;
            break;

          case triton::extlibs::capstone::X86_INS_VPTESTMQ:
            tritonId = triton::arch::x86::ID_INS_VPTESTMQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPTESTNMD:
            tritonId = triton::arch::x86::ID_INS_VPTESTNMD;
            break;

          case triton::extlibs::capstone::X86_INS_VPTESTNMQ:
            tritonId = triton::arch::x86::ID_INS_VPTESTNMQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPTEST:
            tritonId = triton::arch::x86::ID_INS_VPTEST;
            break;

          case triton::extlibs::capstone::X86_INS_VPUNPCKHBW:
            tritonId = triton::arch::x86::ID_INS_VPUNPCKHBW;
            break;

          case triton::extlibs::capstone::X86_INS_VPUNPCKHDQ:
            tritonId = triton::arch::x86::ID_INS_VPUNPCKHDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPUNPCKHQDQ:
            tritonId = triton::arch::x86::ID_INS_VPUNPCKHQDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPUNPCKHWD:
            tritonId = triton::arch::x86::ID_INS_VPUNPCKHWD;
            break;

          case triton::extlibs::capstone::X86_INS_VPUNPCKLBW:
            tritonId = triton::arch::x86::ID_INS_VPUNPCKLBW;
            break;

          case triton::extlibs::capstone::X86_INS_VPUNPCKLDQ:
            tritonId = triton::arch::x86::ID_INS_VPUNPCKLDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPUNPCKLQDQ:
            tritonId = triton::arch::x86::ID_INS_VPUNPCKLQDQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPUNPCKLWD:
            tritonId = triton::arch::x86::ID_INS_VPUNPCKLWD;
            break;

          case triton::extlibs::capstone::X86_INS_VPXORD:
            tritonId = triton::arch::x86::ID_INS_VPXORD;
            break;

          case triton::extlibs::capstone::X86_INS_VPXORQ:
            tritonId = triton::arch::x86::ID_INS_VPXORQ;
            break;

          case triton::extlibs::capstone::X86_INS_VPXOR:
            tritonId = triton::arch::x86::ID_INS_VPXOR;
            break;

          case triton::extlibs::capstone::X86_INS_VRCP14PD:
            tritonId = triton::arch::x86::ID_INS_VRCP14PD;
            break;

          case triton::extlibs::capstone::X86_INS_VRCP14PS:
            tritonId = triton::arch::x86::ID_INS_VRCP14PS;
            break;

          case triton::extlibs::capstone::X86_INS_VRCP14SD:
            tritonId = triton::arch::x86::ID_INS_VRCP14SD;
            break;

          case triton::extlibs::capstone::X86_INS_VRCP14SS:
            tritonId = triton::arch::x86::ID_INS_VRCP14SS;
            break;

          case triton::extlibs::capstone::X86_INS_VRCP28PD:
            tritonId = triton::arch::x86::ID_INS_VRCP28PD;
            break;

          case triton::extlibs::capstone::X86_INS_VRCP28PS:
            tritonId = triton::arch::x86::ID_INS_VRCP28PS;
            break;

          case triton::extlibs::capstone::X86_INS_VRCP28SD:
            tritonId = triton::arch::x86::ID_INS_VRCP28SD;
            break;

          case triton::extlibs::capstone::X86_INS_VRCP28SS:
            tritonId = triton::arch::x86::ID_INS_VRCP28SS;
            break;

          case triton::extlibs::capstone::X86_INS_VRCPPS:
            tritonId = triton::arch::x86::ID_INS_VRCPPS;
            break;

          case triton::extlibs::capstone::X86_INS_VRCPSS:
            tritonId = triton::arch::x86::ID_INS_VRCPSS;
            break;

          case triton::extlibs::capstone::X86_INS_VRNDSCALEPD:
            tritonId = triton::arch::x86::ID_INS_VRNDSCALEPD;
            break;

          case triton::extlibs::capstone::X86_INS_VRNDSCALEPS:
            tritonId = triton::arch::x86::ID_INS_VRNDSCALEPS;
            break;

          case triton::extlibs::capstone::X86_INS_VRNDSCALESD:
            tritonId = triton::arch::x86::ID_INS_VRNDSCALESD;
            break;

          case triton::extlibs::capstone::X86_INS_VRNDSCALESS:
            tritonId = triton::arch::x86::ID_INS_VRNDSCALESS;
            break;

          case triton::extlibs::capstone::X86_INS_VROUNDPD:
            tritonId = triton::arch::x86::ID_INS_VROUNDPD;
            break;

          case triton::extlibs::capstone::X86_INS_VROUNDPS:
            tritonId = triton::arch::x86::ID_INS_VROUNDPS;
            break;

          case triton::extlibs::capstone::X86_INS_VROUNDSD:
            tritonId = triton::arch::x86::ID_INS_VROUNDSD;
            break;

          case triton::extlibs::capstone::X86_INS_VROUNDSS:
            tritonId = triton::arch::x86::ID_INS_VROUNDSS;
            break;

          case triton::extlibs::capstone::X86_INS_VRSQRT14PD:
            tritonId = triton::arch::x86::ID_INS_VRSQRT14PD;
            break;

          case triton::extlibs::capstone::X86_INS_VRSQRT14PS:
            tritonId = triton::arch::x86::ID_INS_VRSQRT14PS;
            break;

          case triton::extlibs::capstone::X86_INS_VRSQRT14SD:
            tritonId = triton::arch::x86::ID_INS_VRSQRT14SD;
            break;

          case triton::extlibs::capstone::X86_INS_VRSQRT14SS:
            tritonId = triton::arch::x86::ID_INS_VRSQRT14SS;
            break;

          case triton::extlibs::capstone::X86_INS_VRSQRT28PD:
            tritonId = triton::arch::x86::ID_INS_VRSQRT28PD;
            break;

          case triton::extlibs::capstone::X86_INS_VRSQRT28PS:
            tritonId = triton::arch::x86::ID_INS_VRSQRT28PS;
            break;

          case triton::extlibs::capstone::X86_INS_VRSQRT28SD:
            tritonId = triton::arch::x86::ID_INS_VRSQRT28SD;
            break;

          case triton::extlibs::capstone::X86_INS_VRSQRT28SS:
            tritonId = triton::arch::x86::ID_INS_VRSQRT28SS;
            break;

          case triton::extlibs::capstone::X86_INS_VRSQRTPS:
            tritonId = triton::arch::x86::ID_INS_VRSQRTPS;
            break;

          case triton::extlibs::capstone::X86_INS_VRSQRTSS:
            tritonId = triton::arch::x86::ID_INS_VRSQRTSS;
            break;

          case triton::extlibs::capstone::X86_INS_VSCATTERDPD:
            tritonId = triton::arch::x86::ID_INS_VSCATTERDPD;
            break;

          case triton::extlibs::capstone::X86_INS_VSCATTERDPS:
            tritonId = triton::arch::x86::ID_INS_VSCATTERDPS;
            break;

          case triton::extlibs::capstone::X86_INS_VSCATTERPF0DPD:
            tritonId = triton::arch::x86::ID_INS_VSCATTERPF0DPD;
            break;

          case triton::extlibs::capstone::X86_INS_VSCATTERPF0DPS:
            tritonId = triton::arch::x86::ID_INS_VSCATTERPF0DPS;
            break;

          case triton::extlibs::capstone::X86_INS_VSCATTERPF0QPD:
            tritonId = triton::arch::x86::ID_INS_VSCATTERPF0QPD;
            break;

          case triton::extlibs::capstone::X86_INS_VSCATTERPF0QPS:
            tritonId = triton::arch::x86::ID_INS_VSCATTERPF0QPS;
            break;

          case triton::extlibs::capstone::X86_INS_VSCATTERPF1DPD:
            tritonId = triton::arch::x86::ID_INS_VSCATTERPF1DPD;
            break;

          case triton::extlibs::capstone::X86_INS_VSCATTERPF1DPS:
            tritonId = triton::arch::x86::ID_INS_VSCATTERPF1DPS;
            break;

          case triton::extlibs::capstone::X86_INS_VSCATTERPF1QPD:
            tritonId = triton::arch::x86::ID_INS_VSCATTERPF1QPD;
            break;

          case triton::extlibs::capstone::X86_INS_VSCATTERPF1QPS:
            tritonId = triton::arch::x86::ID_INS_VSCATTERPF1QPS;
            break;

          case triton::extlibs::capstone::X86_INS_VSCATTERQPD:
            tritonId = triton::arch::x86::ID_INS_VSCATTERQPD;
            break;

          case triton::extlibs::capstone::X86_INS_VSCATTERQPS:
            tritonId = triton::arch::x86::ID_INS_VSCATTERQPS;
            break;

          case triton::extlibs::capstone::X86_INS_VSHUFPD:
            tritonId = triton::arch::x86::ID_INS_VSHUFPD;
            break;

          case triton::extlibs::capstone::X86_INS_VSHUFPS:
            tritonId = triton::arch::x86::ID_INS_VSHUFPS;
            break;

          case triton::extlibs::capstone::X86_INS_VSQRTPD:
            tritonId = triton::arch::x86::ID_INS_VSQRTPD;
            break;

          case triton::extlibs::capstone::X86_INS_VSQRTPS:
            tritonId = triton::arch::x86::ID_INS_VSQRTPS;
            break;

          case triton::extlibs::capstone::X86_INS_VSQRTSD:
            tritonId = triton::arch::x86::ID_INS_VSQRTSD;
            break;

          case triton::extlibs::capstone::X86_INS_VSQRTSS:
            tritonId = triton::arch::x86::ID_INS_VSQRTSS;
            break;

          case triton::extlibs::capstone::X86_INS_VSTMXCSR:
            tritonId = triton::arch::x86::ID_INS_VSTMXCSR;
            break;

          case triton::extlibs::capstone::X86_INS_VSUBPD:
            tritonId = triton::arch::x86::ID_INS_VSUBPD;
            break;

          case triton::extlibs::capstone::X86_INS_VSUBPS:
            tritonId = triton::arch::x86::ID_INS_VSUBPS;
            break;

          case triton::extlibs::capstone::X86_INS_VSUBSD:
            tritonId = triton::arch::x86::ID_INS_VSUBSD;
            break;

          case triton::extlibs::capstone::X86_INS_VSUBSS:
            tritonId = triton::arch::x86::ID_INS_VSUBSS;
            break;

          case triton::extlibs::capstone::X86_INS_VTESTPD:
            tritonId = triton::arch::x86::ID_INS_VTESTPD;
            break;

          case triton::extlibs::capstone::X86_INS_VTESTPS:
            tritonId = triton::arch::x86::ID_INS_VTESTPS;
            break;

          case triton::extlibs::capstone::X86_INS_VUNPCKHPD:
            tritonId = triton::arch::x86::ID_INS_VUNPCKHPD;
            break;

          case triton::extlibs::capstone::X86_INS_VUNPCKHPS:
            tritonId = triton::arch::x86::ID_INS_VUNPCKHPS;
            break;

          case triton::extlibs::capstone::X86_INS_VUNPCKLPD:
            tritonId = triton::arch::x86::ID_INS_VUNPCKLPD;
            break;

          case triton::extlibs::capstone::X86_INS_VUNPCKLPS:
            tritonId = triton::arch::x86::ID_INS_VUNPCKLPS;
            break;

          case triton::extlibs::capstone::X86_INS_VZEROALL:
            tritonId = triton::arch::x86::ID_INS_VZEROALL;
            break;

          case triton::extlibs::capstone::X86_INS_VZEROUPPER:
            tritonId = triton::arch::x86::ID_INS_VZEROUPPER;
            break;

          case triton::extlibs::capstone::X86_INS_WAIT:
            tritonId = triton::arch::x86::ID_INS_WAIT;
            break;

          case triton::extlibs::capstone::X86_INS_WBINVD:
            tritonId = triton::arch::x86::ID_INS_WBINVD;
            break;

          case triton::extlibs::capstone::X86_INS_WRFSBASE:
            tritonId = triton::arch::x86::ID_INS_WRFSBASE;
            break;

          case triton::extlibs::capstone::X86_INS_WRGSBASE:
            tritonId = triton::arch::x86::ID_INS_WRGSBASE;
            break;

          case triton::extlibs::capstone::X86_INS_WRMSR:
            tritonId = triton::arch::x86::ID_INS_WRMSR;
            break;

          case triton::extlibs::capstone::X86_INS_XABORT:
            tritonId = triton::arch::x86::ID_INS_XABORT;
            break;

          case triton::extlibs::capstone::X86_INS_XACQUIRE:
            tritonId = triton::arch::x86::ID_INS_XACQUIRE;
            break;

          case triton::extlibs::capstone::X86_INS_XBEGIN:
            tritonId = triton::arch::x86::ID_INS_XBEGIN;
            break;

          case triton::extlibs::capstone::X86_INS_XCHG:
            tritonId = triton::arch::x86::ID_INS_XCHG;
            break;

          case triton::extlibs::capstone::X86_INS_FXCH:
            tritonId = triton::arch::x86::ID_INS_FXCH;
            break;

          case triton::extlibs::capstone::X86_INS_XCRYPTCBC:
            tritonId = triton::arch::x86::ID_INS_XCRYPTCBC;
            break;

          case triton::extlibs::capstone::X86_INS_XCRYPTCFB:
            tritonId = triton::arch::x86::ID_INS_XCRYPTCFB;
            break;

          case triton::extlibs::capstone::X86_INS_XCRYPTCTR:
            tritonId = triton::arch::x86::ID_INS_XCRYPTCTR;
            break;

          case triton::extlibs::capstone::X86_INS_XCRYPTECB:
            tritonId = triton::arch::x86::ID_INS_XCRYPTECB;
            break;

          case triton::extlibs::capstone::X86_INS_XCRYPTOFB:
            tritonId = triton::arch::x86::ID_INS_XCRYPTOFB;
            break;

          case triton::extlibs::capstone::X86_INS_XEND:
            tritonId = triton::arch::x86::ID_INS_XEND;
            break;

          case triton::extlibs::capstone::X86_INS_XGETBV:
            tritonId = triton::arch::x86::ID_INS_XGETBV;
            break;

          case triton::extlibs::capstone::X86_INS_XLATB:
            tritonId = triton::arch::x86::ID_INS_XLATB;
            break;

          case triton::extlibs::capstone::X86_INS_XRELEASE:
            tritonId = triton::arch::x86::ID_INS_XRELEASE;
            break;

          case triton::extlibs::capstone::X86_INS_XRSTOR:
            tritonId = triton::arch::x86::ID_INS_XRSTOR;
            break;

          case triton::extlibs::capstone::X86_INS_XRSTOR64:
            tritonId = triton::arch::x86::ID_INS_XRSTOR64;
            break;

          case triton::extlibs::capstone::X86_INS_XSAVE:
            tritonId = triton::arch::x86::ID_INS_XSAVE;
            break;

          case triton::extlibs::capstone::X86_INS_XSAVE64:
            tritonId = triton::arch::x86::ID_INS_XSAVE64;
            break;

          case triton::extlibs::capstone::X86_INS_XSAVEOPT:
            tritonId = triton::arch::x86::ID_INS_XSAVEOPT;
            break;

          case triton::extlibs::capstone::X86_INS_XSAVEOPT64:
            tritonId = triton::arch::x86::ID_INS_XSAVEOPT64;
            break;

          case triton::extlibs::capstone::X86_INS_XSETBV:
            tritonId = triton::arch::x86::ID_INS_XSETBV;
            break;

          case triton::extlibs::capstone::X86_INS_XSHA1:
            tritonId = triton::arch::x86::ID_INS_XSHA1;
            break;

          case triton::extlibs::capstone::X86_INS_XSHA256:
            tritonId = triton::arch::x86::ID_INS_XSHA256;
            break;

          case triton::extlibs::capstone::X86_INS_XSTORE:
            tritonId = triton::arch::x86::ID_INS_XSTORE;
            break;

          case triton::extlibs::capstone::X86_INS_XTEST:
            tritonId = triton::arch::x86::ID_INS_XTEST;
            break;

          default:
            tritonId = triton::arch::x86::ID_INST_INVALID;
            break;

        }
        return tritonId;
      }


      triton::uint32 x86Specifications::capstonePrefixToTritonPrefix(triton::uint32 id) const {
        triton::uint32 tritonId = triton::arch::x86::ID_PREFIX_INVALID;

        switch (id) {

          case triton::extlibs::capstone::X86_PREFIX_LOCK:
            tritonId = triton::arch::x86::ID_PREFIX_LOCK;
            break;

          case triton::extlibs::capstone::X86_PREFIX_REP:
            tritonId = triton::arch::x86::ID_PREFIX_REP;
            break;

          case triton::extlibs::capstone::X86_PREFIX_REPNE:
            tritonId = triton::arch::x86::ID_PREFIX_REPNE;
            break;

          default:
            tritonId = triton::arch::x86::ID_PREFIX_INVALID;
            break;

        }
        return tritonId;
      }

    }; /* x86 namespace */
  }; /* arch namespace */
}; /* triton namespace */

