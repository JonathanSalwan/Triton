//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <api.hpp>
#include <capstone/x86.h>
#include <cpuSize.hpp>
#include <x86Specifications.hpp>



namespace triton {
  namespace arch {
    namespace x86 {

      /*
       * Inside semantics, sometime we have to use references to registers.
       * TRITON_X86_REG_RAX, TRITON_X86_REG_RBX, ..., TRITON_X86_REG_AF...
       * are now available for a temporary access to the triton::arch::RegisterOperand
       * class. By default, these X86_REG are empty. We must use init32 or init64 before.
       */

      triton::arch::RegisterOperand x86_reg_rax    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_eax    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_ax     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_ah     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_al     = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_rbx    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_ebx    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_bx     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_bh     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_bl     = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_rcx    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_ecx    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_cx     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_ch     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_cl     = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_rdx    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_edx    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_dx     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_dh     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_dl     = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_rdi    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_edi    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_di     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_dil    = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_rsi    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_esi    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_si     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_sil    = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_rsp    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_esp    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_sp     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_spl    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_stack  = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_rbp    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_ebp    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_bp     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_bpl    = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_rip    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_eip    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_ip     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_pc     = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_rflags = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_eflags = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_flags  = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_r8     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r8d    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r8w    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r8b    = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_r9     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r9d    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r9w    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r9b    = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_r10    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r10d   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r10w   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r10b   = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_r11    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r11d   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r11w   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r11b   = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_r12    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r12d   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r12w   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r12b   = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_r13    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r13d   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r13w   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r13b   = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_r14    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r14d   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r14w   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r14b   = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_r15    = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r15d   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r15w   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_r15b   = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_xmm0   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_xmm1   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_xmm2   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_xmm3   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_xmm4   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_xmm5   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_xmm6   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_xmm7   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_xmm8   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_xmm9   = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_xmm10  = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_xmm11  = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_xmm12  = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_xmm13  = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_xmm14  = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_xmm15  = triton::arch::RegisterOperand();

      triton::arch::RegisterOperand x86_reg_af     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_cf     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_df     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_if     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_of     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_pf     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_sf     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_tf     = triton::arch::RegisterOperand();
      triton::arch::RegisterOperand x86_reg_zf     = triton::arch::RegisterOperand();


      /* Returns all information about a register from its triton id */
      std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> regIdToRegInfo(triton::uint32 reg) {

        std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> ret;

        std::get<0>(ret) = "unknown"; /* name           */
        std::get<1>(ret) = 0;         /* highest bit    */
        std::get<2>(ret) = 0;         /* lower bit      */
        std::get<3>(ret) = 0;         /* higest reg id  */

        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return ret;

        switch (reg) {

          case triton::arch::x86::ID_REG_RAX:
            std::get<0>(ret) = "rax";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_RAX;
            break;

          case triton::arch::x86::ID_REG_EAX:
            std::get<0>(ret) = "eax";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RAX : triton::arch::x86::ID_REG_EAX;
            break;

          case triton::arch::x86::ID_REG_AX:
            std::get<0>(ret) = "ax";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RAX : triton::arch::x86::ID_REG_EAX;
            break;

          case triton::arch::x86::ID_REG_AH:
            std::get<0>(ret) = "ah";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = BYTE_SIZE_BIT;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RAX : triton::arch::x86::ID_REG_EAX;
            break;

          case triton::arch::x86::ID_REG_AL:
            std::get<0>(ret) = "al";
            std::get<1>(ret) = BYTE_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RAX : triton::arch::x86::ID_REG_EAX;
            break;

          case triton::arch::x86::ID_REG_RBX:
            std::get<0>(ret) = "rbx";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_RBX;
            break;

          case triton::arch::x86::ID_REG_EBX:
            std::get<0>(ret) = "ebx";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RBX : triton::arch::x86::ID_REG_EBX;
            break;

          case triton::arch::x86::ID_REG_BX:
            std::get<0>(ret) = "bx";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RBX : triton::arch::x86::ID_REG_EBX;
            break;

          case triton::arch::x86::ID_REG_BH:
            std::get<0>(ret) = "bh";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = BYTE_SIZE_BIT;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RBX : triton::arch::x86::ID_REG_EBX;
            break;

          case triton::arch::x86::ID_REG_BL:
            std::get<0>(ret) = "bl";
            std::get<1>(ret) = BYTE_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RBX : triton::arch::x86::ID_REG_EBX;
            break;

          case triton::arch::x86::ID_REG_RCX:
            std::get<0>(ret) = "rcx";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_RCX;
            break;

          case triton::arch::x86::ID_REG_ECX:
            std::get<0>(ret) = "ecx";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RCX : triton::arch::x86::ID_REG_ECX;
            break;

          case triton::arch::x86::ID_REG_CX:
            std::get<0>(ret) = "cx";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RCX : triton::arch::x86::ID_REG_ECX;
            break;

          case triton::arch::x86::ID_REG_CH:
            std::get<0>(ret) = "ch";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = BYTE_SIZE_BIT;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RCX : triton::arch::x86::ID_REG_ECX;
            break;

          case triton::arch::x86::ID_REG_CL:
            std::get<0>(ret) = "cl";
            std::get<1>(ret) = BYTE_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RCX : triton::arch::x86::ID_REG_ECX;
            break;

          case triton::arch::x86::ID_REG_RDX:
            std::get<0>(ret) = "rdx";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_RDX;
            break;

          case triton::arch::x86::ID_REG_EDX:
            std::get<0>(ret) = "edx";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RDX : triton::arch::x86::ID_REG_EDX;
            break;

          case triton::arch::x86::ID_REG_DX:
            std::get<0>(ret) = "dx";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RDX : triton::arch::x86::ID_REG_EDX;
            break;

          case triton::arch::x86::ID_REG_DH:
            std::get<0>(ret) = "dh";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = BYTE_SIZE_BIT;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RDX : triton::arch::x86::ID_REG_EDX;
            break;

          case triton::arch::x86::ID_REG_DL:
            std::get<0>(ret) = "dl";
            std::get<1>(ret) = BYTE_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RDX : triton::arch::x86::ID_REG_EDX;
            break;

          case triton::arch::x86::ID_REG_RDI:
            std::get<0>(ret) = "rdi";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_RDI;
            break;

          case triton::arch::x86::ID_REG_EDI:
            std::get<0>(ret) = "edi";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RDI : triton::arch::x86::ID_REG_EDI;
            break;

          case triton::arch::x86::ID_REG_DI:
            std::get<0>(ret) = "di";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RDI : triton::arch::x86::ID_REG_EDI;
            break;

          case triton::arch::x86::ID_REG_DIL:
            std::get<0>(ret) = "dil";
            std::get<1>(ret) = BYTE_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RDI : triton::arch::x86::ID_REG_EDI;
            break;

          case triton::arch::x86::ID_REG_RSI:
            std::get<0>(ret) = "rsi";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_RSI;
            break;

          case triton::arch::x86::ID_REG_ESI:
            std::get<0>(ret) = "esi";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RSI : triton::arch::x86::ID_REG_ESI;
            break;

          case triton::arch::x86::ID_REG_SI:
            std::get<0>(ret) = "si";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RSI : triton::arch::x86::ID_REG_ESI;
            break;

          case triton::arch::x86::ID_REG_SIL:
            std::get<0>(ret) = "sil";
            std::get<1>(ret) = BYTE_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RSI : triton::arch::x86::ID_REG_ESI;
            break;

          case triton::arch::x86::ID_REG_RBP:
            std::get<0>(ret) = "rbp";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_RBP;
            break;

          case triton::arch::x86::ID_REG_EBP:
            std::get<0>(ret) = "ebp";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RBP : triton::arch::x86::ID_REG_EBP;
            break;

          case triton::arch::x86::ID_REG_BP:
            std::get<0>(ret) = "bp";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RBP : triton::arch::x86::ID_REG_EBP;
            break;

          case triton::arch::x86::ID_REG_BPL:
            std::get<0>(ret) = "bpl";
            std::get<1>(ret) = BYTE_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RBP : triton::arch::x86::ID_REG_EBP;
            break;

          case triton::arch::x86::ID_REG_RSP:
            std::get<0>(ret) = "rsp";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_RSP;
            break;

          case triton::arch::x86::ID_REG_ESP:
            std::get<0>(ret) = "esp";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RSP : triton::arch::x86::ID_REG_ESP;
            break;

          case triton::arch::x86::ID_REG_SP:
            std::get<0>(ret) = "sp";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RSP : triton::arch::x86::ID_REG_ESP;
            break;

          case triton::arch::x86::ID_REG_SPL:
            std::get<0>(ret) = "spl";
            std::get<1>(ret) = BYTE_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RSP : triton::arch::x86::ID_REG_ESP;
            break;

          case triton::arch::x86::ID_REG_RIP:
            std::get<0>(ret) = "rip";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_RIP;
            break;

          case triton::arch::x86::ID_REG_EIP:
            std::get<0>(ret) = "eip";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RIP : triton::arch::x86::ID_REG_EIP;
            break;

          case triton::arch::x86::ID_REG_IP:
            std::get<0>(ret) = "ip";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RIP : triton::arch::x86::ID_REG_EIP;
            break;

          case triton::arch::x86::ID_REG_RFLAGS:
            std::get<0>(ret) = "rflags";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_RFLAGS;
            break;

          case triton::arch::x86::ID_REG_EFLAGS:
            std::get<0>(ret) = "eflags";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RFLAGS : triton::arch::x86::ID_REG_EFLAGS;
            break;

          case triton::arch::x86::ID_REG_R8:
            std::get<0>(ret) = "r8";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R8;
            break;

          case triton::arch::x86::ID_REG_R8D:
            std::get<0>(ret) = "r8d";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R8;
            break;

          case triton::arch::x86::ID_REG_R8W:
            std::get<0>(ret) = "r8w";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R8;
            break;

          case triton::arch::x86::ID_REG_R8B:
            std::get<0>(ret) = "r8b";
            std::get<1>(ret) = BYTE_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R8;
            break;

          case triton::arch::x86::ID_REG_R9:
            std::get<0>(ret) = "r9";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R9;
            break;

          case triton::arch::x86::ID_REG_R9D:
            std::get<0>(ret) = "r9d";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R9;
            break;

          case triton::arch::x86::ID_REG_R9W:
            std::get<0>(ret) = "r9w";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R9;
            break;

          case triton::arch::x86::ID_REG_R9B:
            std::get<0>(ret) = "r9b";
            std::get<1>(ret) = BYTE_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R9;
            break;

          case triton::arch::x86::ID_REG_R10:
            std::get<0>(ret) = "r10";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R10;
            break;

          case triton::arch::x86::ID_REG_R10D:
            std::get<0>(ret) = "r10d";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R10;
            break;

          case triton::arch::x86::ID_REG_R10W:
            std::get<0>(ret) = "r10w";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R10;
            break;

          case triton::arch::x86::ID_REG_R10B:
            std::get<0>(ret) = "r10b";
            std::get<1>(ret) = BYTE_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R10;
            break;

          case triton::arch::x86::ID_REG_R11:
            std::get<0>(ret) = "r11";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R11;
            break;

          case triton::arch::x86::ID_REG_R11D:
            std::get<0>(ret) = "r11d";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R11;
            break;

          case triton::arch::x86::ID_REG_R11W:
            std::get<0>(ret) = "r11w";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R11;
            break;

          case triton::arch::x86::ID_REG_R11B:
            std::get<0>(ret) = "r11b";
            std::get<1>(ret) = BYTE_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R11;
            break;

          case triton::arch::x86::ID_REG_R12:
            std::get<0>(ret) = "r12";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R12;
            break;

          case triton::arch::x86::ID_REG_R12D:
            std::get<0>(ret) = "r12d";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R12;
            break;

          case triton::arch::x86::ID_REG_R12W:
            std::get<0>(ret) = "r12w";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R12;
            break;

          case triton::arch::x86::ID_REG_R12B:
            std::get<0>(ret) = "r12b";
            std::get<1>(ret) = BYTE_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R12;
            break;

          case triton::arch::x86::ID_REG_R13:
            std::get<0>(ret) = "r13";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R13;
            break;

          case triton::arch::x86::ID_REG_R13D:
            std::get<0>(ret) = "r13d";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R13;
            break;

          case triton::arch::x86::ID_REG_R13W:
            std::get<0>(ret) = "r13w";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R13;
            break;

          case triton::arch::x86::ID_REG_R13B:
            std::get<0>(ret) = "r13b";
            std::get<1>(ret) = BYTE_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R13;
            break;

          case triton::arch::x86::ID_REG_R14:
            std::get<0>(ret) = "r14";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R14;
            break;

          case triton::arch::x86::ID_REG_R14D:
            std::get<0>(ret) = "r14d";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R14;
            break;

          case triton::arch::x86::ID_REG_R14W:
            std::get<0>(ret) = "r14w";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R14;
            break;

          case triton::arch::x86::ID_REG_R14B:
            std::get<0>(ret) = "r14b";
            std::get<1>(ret) = BYTE_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R14;
            break;

          case triton::arch::x86::ID_REG_R15:
            std::get<0>(ret) = "r15";
            std::get<1>(ret) = QWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R15;
            break;

          case triton::arch::x86::ID_REG_R15D:
            std::get<0>(ret) = "r15d";
            std::get<1>(ret) = DWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R15;
            break;

          case triton::arch::x86::ID_REG_R15W:
            std::get<0>(ret) = "r15w";
            std::get<1>(ret) = WORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R15;
            break;

          case triton::arch::x86::ID_REG_R15B:
            std::get<0>(ret) = "r15b";
            std::get<1>(ret) = BYTE_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_R15;
            break;

          case triton::arch::x86::ID_REG_XMM0:
            std::get<0>(ret) = "xmm0";
            std::get<1>(ret) = DQWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_XMM0;
            break;

          case triton::arch::x86::ID_REG_XMM1:
            std::get<0>(ret) = "xmm1";
            std::get<1>(ret) = DQWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_XMM1;
            break;

          case triton::arch::x86::ID_REG_XMM2:
            std::get<0>(ret) = "xmm2";
            std::get<1>(ret) = DQWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_XMM2;
            break;

          case triton::arch::x86::ID_REG_XMM3:
            std::get<0>(ret) = "xmm3";
            std::get<1>(ret) = DQWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_XMM3;
            break;

          case triton::arch::x86::ID_REG_XMM4:
            std::get<0>(ret) = "xmm4";
            std::get<1>(ret) = DQWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_XMM4;
            break;

          case triton::arch::x86::ID_REG_XMM5:
            std::get<0>(ret) = "xmm5";
            std::get<1>(ret) = DQWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_XMM5;
            break;

          case triton::arch::x86::ID_REG_XMM6:
            std::get<0>(ret) = "xmm6";
            std::get<1>(ret) = DQWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_XMM6;
            break;

          case triton::arch::x86::ID_REG_XMM7:
            std::get<0>(ret) = "xmm7";
            std::get<1>(ret) = DQWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_XMM7;
            break;

          case triton::arch::x86::ID_REG_XMM8:
            std::get<0>(ret) = "xmm8";
            std::get<1>(ret) = DQWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_XMM8;
            break;

          case triton::arch::x86::ID_REG_XMM9:
            std::get<0>(ret) = "xmm9";
            std::get<1>(ret) = DQWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_XMM9;
            break;

          case triton::arch::x86::ID_REG_XMM10:
            std::get<0>(ret) = "xmm10";
            std::get<1>(ret) = DQWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_XMM10;
            break;

          case triton::arch::x86::ID_REG_XMM11:
            std::get<0>(ret) = "xmm11";
            std::get<1>(ret) = DQWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_XMM11;
            break;

          case triton::arch::x86::ID_REG_XMM12:
            std::get<0>(ret) = "xmm12";
            std::get<1>(ret) = DQWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_XMM12;
            break;

          case triton::arch::x86::ID_REG_XMM13:
            std::get<0>(ret) = "xmm13";
            std::get<1>(ret) = DQWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_XMM13;
            break;

          case triton::arch::x86::ID_REG_XMM14:
            std::get<0>(ret) = "xmm14";
            std::get<1>(ret) = DQWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_XMM14;
            break;

          case triton::arch::x86::ID_REG_XMM15:
            std::get<0>(ret) = "xmm15";
            std::get<1>(ret) = DQWORD_SIZE_BIT-1;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_XMM15;
            break;

          case triton::arch::x86::ID_REG_AF:
            std::get<0>(ret) = "af";
            std::get<1>(ret) = 0;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_AF;
            break;

          case triton::arch::x86::ID_REG_CF:
            std::get<0>(ret) = "cf";
            std::get<1>(ret) = 0;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_CF;
            break;

          case triton::arch::x86::ID_REG_DF:
            std::get<0>(ret) = "df";
            std::get<1>(ret) = 0;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_DF;
            break;

          case triton::arch::x86::ID_REG_IF:
            std::get<0>(ret) = "if";
            std::get<1>(ret) = 0;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_IF;
            break;

          case triton::arch::x86::ID_REG_OF:
            std::get<0>(ret) = "of";
            std::get<1>(ret) = 0;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_OF;
            break;

          case triton::arch::x86::ID_REG_PF:
            std::get<0>(ret) = "pf";
            std::get<1>(ret) = 0;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_PF;
            break;

          case triton::arch::x86::ID_REG_SF:
            std::get<0>(ret) = "sf";
            std::get<1>(ret) = 0;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_SF;
            break;

          case triton::arch::x86::ID_REG_TF:
            std::get<0>(ret) = "tf";
            std::get<1>(ret) = 0;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_TF;
            break;

          case triton::arch::x86::ID_REG_ZF:
            std::get<0>(ret) = "zf";
            std::get<1>(ret) = 0;
            std::get<2>(ret) = 0;
            std::get<3>(ret) = triton::arch::x86::ID_REG_ZF;
            break;

        }
        return ret;
      }


      /* Converts a capstone's register id to a triton's register id */
      triton::uint32 capstoneRegToTritonReg(triton::uint32 id) {
        triton::uint32 tritonId = triton::arch::x86::ID_REG_INVALID;

        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return tritonId;

        switch (id) {

          case X86_REG_RAX:
            tritonId = triton::arch::x86::ID_REG_RAX;
            break;

          case X86_REG_EAX:
            tritonId = triton::arch::x86::ID_REG_EAX;
            break;

          case X86_REG_AX:
            tritonId = triton::arch::x86::ID_REG_AX;
            break;

          case X86_REG_AH:
            tritonId = triton::arch::x86::ID_REG_AH;
            break;

          case X86_REG_AL:
            tritonId = triton::arch::x86::ID_REG_AL;
            break;

          case X86_REG_RBX:
            tritonId = triton::arch::x86::ID_REG_RBX;
            break;

          case X86_REG_EBX:
            tritonId = triton::arch::x86::ID_REG_EBX;
            break;

          case X86_REG_BX:
            tritonId = triton::arch::x86::ID_REG_BX;
            break;

          case X86_REG_BH:
            tritonId = triton::arch::x86::ID_REG_BH;
            break;

          case X86_REG_BL:
            tritonId = triton::arch::x86::ID_REG_BL;
            break;

          case X86_REG_RCX:
            tritonId = triton::arch::x86::ID_REG_RCX;
            break;

          case X86_REG_ECX:
            tritonId = triton::arch::x86::ID_REG_ECX;
            break;

          case X86_REG_CX:
            tritonId = triton::arch::x86::ID_REG_CX;
            break;

          case X86_REG_CH:
            tritonId = triton::arch::x86::ID_REG_CH;
            break;

          case X86_REG_CL:
            tritonId = triton::arch::x86::ID_REG_CL;
            break;

          case X86_REG_RDX:
            tritonId = triton::arch::x86::ID_REG_RDX;
            break;

          case X86_REG_EDX:
            tritonId = triton::arch::x86::ID_REG_EDX;
            break;

          case X86_REG_DX:
            tritonId = triton::arch::x86::ID_REG_DX;
            break;

          case X86_REG_DH:
            tritonId = triton::arch::x86::ID_REG_DH;
            break;

          case X86_REG_DL:
            tritonId = triton::arch::x86::ID_REG_DL;
            break;

          case X86_REG_RDI:
            tritonId = triton::arch::x86::ID_REG_RDI;
            break;

          case X86_REG_EDI:
            tritonId = triton::arch::x86::ID_REG_EDI;
            break;

          case X86_REG_DI:
            tritonId = triton::arch::x86::ID_REG_DI;
            break;

          case X86_REG_DIL:
            tritonId = triton::arch::x86::ID_REG_DIL;
            break;

          case X86_REG_RSI:
            tritonId = triton::arch::x86::ID_REG_RSI;
            break;

          case X86_REG_ESI:
            tritonId = triton::arch::x86::ID_REG_ESI;
            break;

          case X86_REG_SI:
            tritonId = triton::arch::x86::ID_REG_SI;
            break;

          case X86_REG_SIL:
            tritonId = triton::arch::x86::ID_REG_SIL;
            break;

          case X86_REG_RBP:
            tritonId = triton::arch::x86::ID_REG_RBP;
            break;

          case X86_REG_EBP:
            tritonId = triton::arch::x86::ID_REG_EBP;
            break;

          case X86_REG_BP:
            tritonId = triton::arch::x86::ID_REG_BP;
            break;

          case X86_REG_BPL:
            tritonId = triton::arch::x86::ID_REG_BPL;
            break;

          case X86_REG_RSP:
            tritonId = triton::arch::x86::ID_REG_RSP;
            break;

          case X86_REG_ESP:
            tritonId = triton::arch::x86::ID_REG_ESP;
            break;

          case X86_REG_SP:
            tritonId = triton::arch::x86::ID_REG_SP;
            break;

          case X86_REG_SPL:
            tritonId = triton::arch::x86::ID_REG_SPL;
            break;

          case X86_REG_RIP:
            tritonId = triton::arch::x86::ID_REG_RIP;
            break;

          case X86_REG_EIP:
            tritonId = triton::arch::x86::ID_REG_EIP;
            break;

          case X86_REG_IP:
            tritonId = triton::arch::x86::ID_REG_IP;
            break;

          case X86_REG_EFLAGS:
            tritonId = (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) ? triton::arch::x86::ID_REG_RFLAGS : triton::arch::x86::ID_REG_EFLAGS;
            break;

          case X86_REG_R8:
            tritonId = triton::arch::x86::ID_REG_R8;
            break;

          case X86_REG_R8D:
            tritonId = triton::arch::x86::ID_REG_R8D;
            break;

          case X86_REG_R8W:
            tritonId = triton::arch::x86::ID_REG_R8W;
            break;

          case X86_REG_R8B:
            tritonId = triton::arch::x86::ID_REG_R8B;
            break;

          case X86_REG_R9:
            tritonId = triton::arch::x86::ID_REG_R9;
            break;

          case X86_REG_R9D:
            tritonId = triton::arch::x86::ID_REG_R9D;
            break;

          case X86_REG_R9W:
            tritonId = triton::arch::x86::ID_REG_R9W;
            break;

          case X86_REG_R9B:
            tritonId = triton::arch::x86::ID_REG_R9B;
            break;

          case X86_REG_R10:
            tritonId = triton::arch::x86::ID_REG_R10;
            break;

          case X86_REG_R10D:
            tritonId = triton::arch::x86::ID_REG_R10D;
            break;

          case X86_REG_R10W:
            tritonId = triton::arch::x86::ID_REG_R10W;
            break;

          case X86_REG_R10B:
            tritonId = triton::arch::x86::ID_REG_R10B;
            break;

          case X86_REG_R11:
            tritonId = triton::arch::x86::ID_REG_R11;
            break;

          case X86_REG_R11D:
            tritonId = triton::arch::x86::ID_REG_R11D;
            break;

          case X86_REG_R11W:
            tritonId = triton::arch::x86::ID_REG_R11W;
            break;

          case X86_REG_R11B:
            tritonId = triton::arch::x86::ID_REG_R11B;
            break;

          case X86_REG_R12:
            tritonId = triton::arch::x86::ID_REG_R12;
            break;

          case X86_REG_R12D:
            tritonId = triton::arch::x86::ID_REG_R12D;
            break;

          case X86_REG_R12W:
            tritonId = triton::arch::x86::ID_REG_R12W;
            break;

          case X86_REG_R12B:
            tritonId = triton::arch::x86::ID_REG_R12B;
            break;

          case X86_REG_R13:
            tritonId = triton::arch::x86::ID_REG_R13;
            break;

          case X86_REG_R13D:
            tritonId = triton::arch::x86::ID_REG_R13D;
            break;

          case X86_REG_R13W:
            tritonId = triton::arch::x86::ID_REG_R13W;
            break;

          case X86_REG_R13B:
            tritonId = triton::arch::x86::ID_REG_R13B;
            break;

          case X86_REG_R14:
            tritonId = triton::arch::x86::ID_REG_R14;
            break;

          case X86_REG_R14D:
            tritonId = triton::arch::x86::ID_REG_R14D;
            break;

          case X86_REG_R14W:
            tritonId = triton::arch::x86::ID_REG_R14W;
            break;

          case X86_REG_R14B:
            tritonId = triton::arch::x86::ID_REG_R14B;
            break;

          case X86_REG_R15:
            tritonId = triton::arch::x86::ID_REG_R15;
            break;

          case X86_REG_R15D:
            tritonId = triton::arch::x86::ID_REG_R15D;
            break;

          case X86_REG_R15W:
            tritonId = triton::arch::x86::ID_REG_R15W;
            break;

          case X86_REG_R15B:
            tritonId = triton::arch::x86::ID_REG_R15B;
            break;

          case X86_REG_XMM0:
            tritonId = triton::arch::x86::ID_REG_XMM0;
            break;

          case X86_REG_XMM1:
            tritonId = triton::arch::x86::ID_REG_XMM1;
            break;

          case X86_REG_XMM2:
            tritonId = triton::arch::x86::ID_REG_XMM2;
            break;

          case X86_REG_XMM3:
            tritonId = triton::arch::x86::ID_REG_XMM3;
            break;

          case X86_REG_XMM4:
            tritonId = triton::arch::x86::ID_REG_XMM4;
            break;

          case X86_REG_XMM5:
            tritonId = triton::arch::x86::ID_REG_XMM5;
            break;

          case X86_REG_XMM6:
            tritonId = triton::arch::x86::ID_REG_XMM6;
            break;

          case X86_REG_XMM7:
            tritonId = triton::arch::x86::ID_REG_XMM7;
            break;

          case X86_REG_XMM8:
            tritonId = triton::arch::x86::ID_REG_XMM8;
            break;

          case X86_REG_XMM9:
            tritonId = triton::arch::x86::ID_REG_XMM9;
            break;

          case X86_REG_XMM10:
            tritonId = triton::arch::x86::ID_REG_XMM10;
            break;

          case X86_REG_XMM11:
            tritonId = triton::arch::x86::ID_REG_XMM11;
            break;

          case X86_REG_XMM12:
            tritonId = triton::arch::x86::ID_REG_XMM12;
            break;

          case X86_REG_XMM13:
            tritonId = triton::arch::x86::ID_REG_XMM13;
            break;

          case X86_REG_XMM14:
            tritonId = triton::arch::x86::ID_REG_XMM14;
            break;

          case X86_REG_XMM15:
            tritonId = triton::arch::x86::ID_REG_XMM15;
            break;

          default:
            tritonId = triton::arch::x86::ID_REG_INVALID;
            break;

        }
        return tritonId;
      }


      /* Converts a capstone's instruction id to a triton's instruction id */
      triton::uint32 capstoneInstToTritonInst(triton::uint32 id) {
        triton::uint32 tritonId = triton::arch::x86::ID_INST_INVALID;

        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return tritonId;

        switch (id) {

          case X86_INS_INVALID:
            tritonId = triton::arch::x86::ID_INST_INVALID;
            break;

          case X86_INS_AAA:
            tritonId = triton::arch::x86::ID_INS_AAA;
            break;

          case X86_INS_AAD:
            tritonId = triton::arch::x86::ID_INS_AAD;
            break;

          case X86_INS_AAM:
            tritonId = triton::arch::x86::ID_INS_AAM;
            break;

          case X86_INS_AAS:
            tritonId = triton::arch::x86::ID_INS_AAS;
            break;

          case X86_INS_FABS:
            tritonId = triton::arch::x86::ID_INS_FABS;
            break;

          case X86_INS_ADC:
            tritonId = triton::arch::x86::ID_INS_ADC;
            break;

          case X86_INS_ADCX:
            tritonId = triton::arch::x86::ID_INS_ADCX;
            break;

          case X86_INS_ADD:
            tritonId = triton::arch::x86::ID_INS_ADD;
            break;

          case X86_INS_ADDPD:
            tritonId = triton::arch::x86::ID_INS_ADDPD;
            break;

          case X86_INS_ADDPS:
            tritonId = triton::arch::x86::ID_INS_ADDPS;
            break;

          case X86_INS_ADDSD:
            tritonId = triton::arch::x86::ID_INS_ADDSD;
            break;

          case X86_INS_ADDSS:
            tritonId = triton::arch::x86::ID_INS_ADDSS;
            break;

          case X86_INS_ADDSUBPD:
            tritonId = triton::arch::x86::ID_INS_ADDSUBPD;
            break;

          case X86_INS_ADDSUBPS:
            tritonId = triton::arch::x86::ID_INS_ADDSUBPS;
            break;

          case X86_INS_FADD:
            tritonId = triton::arch::x86::ID_INS_FADD;
            break;

          case X86_INS_FIADD:
            tritonId = triton::arch::x86::ID_INS_FIADD;
            break;

          case X86_INS_FADDP:
            tritonId = triton::arch::x86::ID_INS_FADDP;
            break;

          case X86_INS_ADOX:
            tritonId = triton::arch::x86::ID_INS_ADOX;
            break;

          case X86_INS_AESDECLAST:
            tritonId = triton::arch::x86::ID_INS_AESDECLAST;
            break;

          case X86_INS_AESDEC:
            tritonId = triton::arch::x86::ID_INS_AESDEC;
            break;

          case X86_INS_AESENCLAST:
            tritonId = triton::arch::x86::ID_INS_AESENCLAST;
            break;

          case X86_INS_AESENC:
            tritonId = triton::arch::x86::ID_INS_AESENC;
            break;

          case X86_INS_AESIMC:
            tritonId = triton::arch::x86::ID_INS_AESIMC;
            break;

          case X86_INS_AESKEYGENASSIST:
            tritonId = triton::arch::x86::ID_INS_AESKEYGENASSIST;
            break;

          case X86_INS_AND:
            tritonId = triton::arch::x86::ID_INS_AND;
            break;

          case X86_INS_ANDN:
            tritonId = triton::arch::x86::ID_INS_ANDN;
            break;

          case X86_INS_ANDNPD:
            tritonId = triton::arch::x86::ID_INS_ANDNPD;
            break;

          case X86_INS_ANDNPS:
            tritonId = triton::arch::x86::ID_INS_ANDNPS;
            break;

          case X86_INS_ANDPD:
            tritonId = triton::arch::x86::ID_INS_ANDPD;
            break;

          case X86_INS_ANDPS:
            tritonId = triton::arch::x86::ID_INS_ANDPS;
            break;

          case X86_INS_ARPL:
            tritonId = triton::arch::x86::ID_INS_ARPL;
            break;

          case X86_INS_BEXTR:
            tritonId = triton::arch::x86::ID_INS_BEXTR;
            break;

          case X86_INS_BLCFILL:
            tritonId = triton::arch::x86::ID_INS_BLCFILL;
            break;

          case X86_INS_BLCI:
            tritonId = triton::arch::x86::ID_INS_BLCI;
            break;

          case X86_INS_BLCIC:
            tritonId = triton::arch::x86::ID_INS_BLCIC;
            break;

          case X86_INS_BLCMSK:
            tritonId = triton::arch::x86::ID_INS_BLCMSK;
            break;

          case X86_INS_BLCS:
            tritonId = triton::arch::x86::ID_INS_BLCS;
            break;

          case X86_INS_BLENDPD:
            tritonId = triton::arch::x86::ID_INS_BLENDPD;
            break;

          case X86_INS_BLENDPS:
            tritonId = triton::arch::x86::ID_INS_BLENDPS;
            break;

          case X86_INS_BLENDVPD:
            tritonId = triton::arch::x86::ID_INS_BLENDVPD;
            break;

          case X86_INS_BLENDVPS:
            tritonId = triton::arch::x86::ID_INS_BLENDVPS;
            break;

          case X86_INS_BLSFILL:
            tritonId = triton::arch::x86::ID_INS_BLSFILL;
            break;

          case X86_INS_BLSI:
            tritonId = triton::arch::x86::ID_INS_BLSI;
            break;

          case X86_INS_BLSIC:
            tritonId = triton::arch::x86::ID_INS_BLSIC;
            break;

          case X86_INS_BLSMSK:
            tritonId = triton::arch::x86::ID_INS_BLSMSK;
            break;

          case X86_INS_BLSR:
            tritonId = triton::arch::x86::ID_INS_BLSR;
            break;

          case X86_INS_BOUND:
            tritonId = triton::arch::x86::ID_INS_BOUND;
            break;

          case X86_INS_BSF:
            tritonId = triton::arch::x86::ID_INS_BSF;
            break;

          case X86_INS_BSR:
            tritonId = triton::arch::x86::ID_INS_BSR;
            break;

          case X86_INS_BSWAP:
            tritonId = triton::arch::x86::ID_INS_BSWAP;
            break;

          case X86_INS_BT:
            tritonId = triton::arch::x86::ID_INS_BT;
            break;

          case X86_INS_BTC:
            tritonId = triton::arch::x86::ID_INS_BTC;
            break;

          case X86_INS_BTR:
            tritonId = triton::arch::x86::ID_INS_BTR;
            break;

          case X86_INS_BTS:
            tritonId = triton::arch::x86::ID_INS_BTS;
            break;

          case X86_INS_BZHI:
            tritonId = triton::arch::x86::ID_INS_BZHI;
            break;

          case X86_INS_CALL:
            tritonId = triton::arch::x86::ID_INS_CALL;
            break;

          case X86_INS_CBW:
            tritonId = triton::arch::x86::ID_INS_CBW;
            break;

          case X86_INS_CDQ:
            tritonId = triton::arch::x86::ID_INS_CDQ;
            break;

          case X86_INS_CDQE:
            tritonId = triton::arch::x86::ID_INS_CDQE;
            break;

          case X86_INS_FCHS:
            tritonId = triton::arch::x86::ID_INS_FCHS;
            break;

          case X86_INS_CLAC:
            tritonId = triton::arch::x86::ID_INS_CLAC;
            break;

          case X86_INS_CLC:
            tritonId = triton::arch::x86::ID_INS_CLC;
            break;

          case X86_INS_CLD:
            tritonId = triton::arch::x86::ID_INS_CLD;
            break;

          case X86_INS_CLFLUSH:
            tritonId = triton::arch::x86::ID_INS_CLFLUSH;
            break;

          case X86_INS_CLGI:
            tritonId = triton::arch::x86::ID_INS_CLGI;
            break;

          case X86_INS_CLI:
            tritonId = triton::arch::x86::ID_INS_CLI;
            break;

          case X86_INS_CLTS:
            tritonId = triton::arch::x86::ID_INS_CLTS;
            break;

          case X86_INS_CMC:
            tritonId = triton::arch::x86::ID_INS_CMC;
            break;

          case X86_INS_CMOVA:
            tritonId = triton::arch::x86::ID_INS_CMOVA;
            break;

          case X86_INS_CMOVAE:
            tritonId = triton::arch::x86::ID_INS_CMOVAE;
            break;

          case X86_INS_CMOVB:
            tritonId = triton::arch::x86::ID_INS_CMOVB;
            break;

          case X86_INS_CMOVBE:
            tritonId = triton::arch::x86::ID_INS_CMOVBE;
            break;

          case X86_INS_FCMOVBE:
            tritonId = triton::arch::x86::ID_INS_FCMOVBE;
            break;

          case X86_INS_FCMOVB:
            tritonId = triton::arch::x86::ID_INS_FCMOVB;
            break;

          case X86_INS_CMOVE:
            tritonId = triton::arch::x86::ID_INS_CMOVE;
            break;

          case X86_INS_FCMOVE:
            tritonId = triton::arch::x86::ID_INS_FCMOVE;
            break;

          case X86_INS_CMOVG:
            tritonId = triton::arch::x86::ID_INS_CMOVG;
            break;

          case X86_INS_CMOVGE:
            tritonId = triton::arch::x86::ID_INS_CMOVGE;
            break;

          case X86_INS_CMOVL:
            tritonId = triton::arch::x86::ID_INS_CMOVL;
            break;

          case X86_INS_CMOVLE:
            tritonId = triton::arch::x86::ID_INS_CMOVLE;
            break;

          case X86_INS_FCMOVNBE:
            tritonId = triton::arch::x86::ID_INS_FCMOVNBE;
            break;

          case X86_INS_FCMOVNB:
            tritonId = triton::arch::x86::ID_INS_FCMOVNB;
            break;

          case X86_INS_CMOVNE:
            tritonId = triton::arch::x86::ID_INS_CMOVNE;
            break;

          case X86_INS_FCMOVNE:
            tritonId = triton::arch::x86::ID_INS_FCMOVNE;
            break;

          case X86_INS_CMOVNO:
            tritonId = triton::arch::x86::ID_INS_CMOVNO;
            break;

          case X86_INS_CMOVNP:
            tritonId = triton::arch::x86::ID_INS_CMOVNP;
            break;

          case X86_INS_FCMOVNU:
            tritonId = triton::arch::x86::ID_INS_FCMOVNU;
            break;

          case X86_INS_CMOVNS:
            tritonId = triton::arch::x86::ID_INS_CMOVNS;
            break;

          case X86_INS_CMOVO:
            tritonId = triton::arch::x86::ID_INS_CMOVO;
            break;

          case X86_INS_CMOVP:
            tritonId = triton::arch::x86::ID_INS_CMOVP;
            break;

          case X86_INS_FCMOVU:
            tritonId = triton::arch::x86::ID_INS_FCMOVU;
            break;

          case X86_INS_CMOVS:
            tritonId = triton::arch::x86::ID_INS_CMOVS;
            break;

          case X86_INS_CMP:
            tritonId = triton::arch::x86::ID_INS_CMP;
            break;

          case X86_INS_CMPPD:
            tritonId = triton::arch::x86::ID_INS_CMPPD;
            break;

          case X86_INS_CMPPS:
            tritonId = triton::arch::x86::ID_INS_CMPPS;
            break;

          case X86_INS_CMPSB:
            tritonId = triton::arch::x86::ID_INS_CMPSB;
            break;

          case X86_INS_CMPSD:
            tritonId = triton::arch::x86::ID_INS_CMPSD;
            break;

          case X86_INS_CMPSQ:
            tritonId = triton::arch::x86::ID_INS_CMPSQ;
            break;

          case X86_INS_CMPSS:
            tritonId = triton::arch::x86::ID_INS_CMPSS;
            break;

          case X86_INS_CMPSW:
            tritonId = triton::arch::x86::ID_INS_CMPSW;
            break;

          case X86_INS_CMPXCHG16B:
            tritonId = triton::arch::x86::ID_INS_CMPXCHG16B;
            break;

          case X86_INS_CMPXCHG:
            tritonId = triton::arch::x86::ID_INS_CMPXCHG;
            break;

          case X86_INS_CMPXCHG8B:
            tritonId = triton::arch::x86::ID_INS_CMPXCHG8B;
            break;

          case X86_INS_COMISD:
            tritonId = triton::arch::x86::ID_INS_COMISD;
            break;

          case X86_INS_COMISS:
            tritonId = triton::arch::x86::ID_INS_COMISS;
            break;

          case X86_INS_FCOMP:
            tritonId = triton::arch::x86::ID_INS_FCOMP;
            break;

          case X86_INS_FCOMPI:
            tritonId = triton::arch::x86::ID_INS_FCOMPI;
            break;

          case X86_INS_FCOMI:
            tritonId = triton::arch::x86::ID_INS_FCOMI;
            break;

          case X86_INS_FCOM:
            tritonId = triton::arch::x86::ID_INS_FCOM;
            break;

          case X86_INS_FCOS:
            tritonId = triton::arch::x86::ID_INS_FCOS;
            break;

          case X86_INS_CPUID:
            tritonId = triton::arch::x86::ID_INS_CPUID;
            break;

          case X86_INS_CQO:
            tritonId = triton::arch::x86::ID_INS_CQO;
            break;

          case X86_INS_CRC32:
            tritonId = triton::arch::x86::ID_INS_CRC32;
            break;

          case X86_INS_CVTDQ2PD:
            tritonId = triton::arch::x86::ID_INS_CVTDQ2PD;
            break;

          case X86_INS_CVTDQ2PS:
            tritonId = triton::arch::x86::ID_INS_CVTDQ2PS;
            break;

          case X86_INS_CVTPD2DQ:
            tritonId = triton::arch::x86::ID_INS_CVTPD2DQ;
            break;

          case X86_INS_CVTPD2PS:
            tritonId = triton::arch::x86::ID_INS_CVTPD2PS;
            break;

          case X86_INS_CVTPS2DQ:
            tritonId = triton::arch::x86::ID_INS_CVTPS2DQ;
            break;

          case X86_INS_CVTPS2PD:
            tritonId = triton::arch::x86::ID_INS_CVTPS2PD;
            break;

          case X86_INS_CVTSD2SI:
            tritonId = triton::arch::x86::ID_INS_CVTSD2SI;
            break;

          case X86_INS_CVTSD2SS:
            tritonId = triton::arch::x86::ID_INS_CVTSD2SS;
            break;

          case X86_INS_CVTSI2SD:
            tritonId = triton::arch::x86::ID_INS_CVTSI2SD;
            break;

          case X86_INS_CVTSI2SS:
            tritonId = triton::arch::x86::ID_INS_CVTSI2SS;
            break;

          case X86_INS_CVTSS2SD:
            tritonId = triton::arch::x86::ID_INS_CVTSS2SD;
            break;

          case X86_INS_CVTSS2SI:
            tritonId = triton::arch::x86::ID_INS_CVTSS2SI;
            break;

          case X86_INS_CVTTPD2DQ:
            tritonId = triton::arch::x86::ID_INS_CVTTPD2DQ;
            break;

          case X86_INS_CVTTPS2DQ:
            tritonId = triton::arch::x86::ID_INS_CVTTPS2DQ;
            break;

          case X86_INS_CVTTSD2SI:
            tritonId = triton::arch::x86::ID_INS_CVTTSD2SI;
            break;

          case X86_INS_CVTTSS2SI:
            tritonId = triton::arch::x86::ID_INS_CVTTSS2SI;
            break;

          case X86_INS_CWD:
            tritonId = triton::arch::x86::ID_INS_CWD;
            break;

          case X86_INS_CWDE:
            tritonId = triton::arch::x86::ID_INS_CWDE;
            break;

          case X86_INS_DAA:
            tritonId = triton::arch::x86::ID_INS_DAA;
            break;

          case X86_INS_DAS:
            tritonId = triton::arch::x86::ID_INS_DAS;
            break;

          case X86_INS_DATA16:
            tritonId = triton::arch::x86::ID_INS_DATA16;
            break;

          case X86_INS_DEC:
            tritonId = triton::arch::x86::ID_INS_DEC;
            break;

          case X86_INS_DIV:
            tritonId = triton::arch::x86::ID_INS_DIV;
            break;

          case X86_INS_DIVPD:
            tritonId = triton::arch::x86::ID_INS_DIVPD;
            break;

          case X86_INS_DIVPS:
            tritonId = triton::arch::x86::ID_INS_DIVPS;
            break;

          case X86_INS_FDIVR:
            tritonId = triton::arch::x86::ID_INS_FDIVR;
            break;

          case X86_INS_FIDIVR:
            tritonId = triton::arch::x86::ID_INS_FIDIVR;
            break;

          case X86_INS_FDIVRP:
            tritonId = triton::arch::x86::ID_INS_FDIVRP;
            break;

          case X86_INS_DIVSD:
            tritonId = triton::arch::x86::ID_INS_DIVSD;
            break;

          case X86_INS_DIVSS:
            tritonId = triton::arch::x86::ID_INS_DIVSS;
            break;

          case X86_INS_FDIV:
            tritonId = triton::arch::x86::ID_INS_FDIV;
            break;

          case X86_INS_FIDIV:
            tritonId = triton::arch::x86::ID_INS_FIDIV;
            break;

          case X86_INS_FDIVP:
            tritonId = triton::arch::x86::ID_INS_FDIVP;
            break;

          case X86_INS_DPPD:
            tritonId = triton::arch::x86::ID_INS_DPPD;
            break;

          case X86_INS_DPPS:
            tritonId = triton::arch::x86::ID_INS_DPPS;
            break;

          case X86_INS_RET:
            tritonId = triton::arch::x86::ID_INS_RET;
            break;

          case X86_INS_ENCLS:
            tritonId = triton::arch::x86::ID_INS_ENCLS;
            break;

          case X86_INS_ENCLU:
            tritonId = triton::arch::x86::ID_INS_ENCLU;
            break;

          case X86_INS_ENTER:
            tritonId = triton::arch::x86::ID_INS_ENTER;
            break;

          case X86_INS_EXTRACTPS:
            tritonId = triton::arch::x86::ID_INS_EXTRACTPS;
            break;

          case X86_INS_EXTRQ:
            tritonId = triton::arch::x86::ID_INS_EXTRQ;
            break;

          case X86_INS_F2XM1:
            tritonId = triton::arch::x86::ID_INS_F2XM1;
            break;

          case X86_INS_LCALL:
            tritonId = triton::arch::x86::ID_INS_LCALL;
            break;

          case X86_INS_LJMP:
            tritonId = triton::arch::x86::ID_INS_LJMP;
            break;

          case X86_INS_FBLD:
            tritonId = triton::arch::x86::ID_INS_FBLD;
            break;

          case X86_INS_FBSTP:
            tritonId = triton::arch::x86::ID_INS_FBSTP;
            break;

          case X86_INS_FCOMPP:
            tritonId = triton::arch::x86::ID_INS_FCOMPP;
            break;

          case X86_INS_FDECSTP:
            tritonId = triton::arch::x86::ID_INS_FDECSTP;
            break;

          case X86_INS_FEMMS:
            tritonId = triton::arch::x86::ID_INS_FEMMS;
            break;

          case X86_INS_FFREE:
            tritonId = triton::arch::x86::ID_INS_FFREE;
            break;

          case X86_INS_FICOM:
            tritonId = triton::arch::x86::ID_INS_FICOM;
            break;

          case X86_INS_FICOMP:
            tritonId = triton::arch::x86::ID_INS_FICOMP;
            break;

          case X86_INS_FINCSTP:
            tritonId = triton::arch::x86::ID_INS_FINCSTP;
            break;

          case X86_INS_FLDCW:
            tritonId = triton::arch::x86::ID_INS_FLDCW;
            break;

          case X86_INS_FLDENV:
            tritonId = triton::arch::x86::ID_INS_FLDENV;
            break;

          case X86_INS_FLDL2E:
            tritonId = triton::arch::x86::ID_INS_FLDL2E;
            break;

          case X86_INS_FLDL2T:
            tritonId = triton::arch::x86::ID_INS_FLDL2T;
            break;

          case X86_INS_FLDLG2:
            tritonId = triton::arch::x86::ID_INS_FLDLG2;
            break;

          case X86_INS_FLDLN2:
            tritonId = triton::arch::x86::ID_INS_FLDLN2;
            break;

          case X86_INS_FLDPI:
            tritonId = triton::arch::x86::ID_INS_FLDPI;
            break;

          case X86_INS_FNCLEX:
            tritonId = triton::arch::x86::ID_INS_FNCLEX;
            break;

          case X86_INS_FNINIT:
            tritonId = triton::arch::x86::ID_INS_FNINIT;
            break;

          case X86_INS_FNOP:
            tritonId = triton::arch::x86::ID_INS_FNOP;
            break;

          case X86_INS_FNSTCW:
            tritonId = triton::arch::x86::ID_INS_FNSTCW;
            break;

          case X86_INS_FNSTSW:
            tritonId = triton::arch::x86::ID_INS_FNSTSW;
            break;

          case X86_INS_FPATAN:
            tritonId = triton::arch::x86::ID_INS_FPATAN;
            break;

          case X86_INS_FPREM:
            tritonId = triton::arch::x86::ID_INS_FPREM;
            break;

          case X86_INS_FPREM1:
            tritonId = triton::arch::x86::ID_INS_FPREM1;
            break;

          case X86_INS_FPTAN:
            tritonId = triton::arch::x86::ID_INS_FPTAN;
            break;

          case X86_INS_FRNDINT:
            tritonId = triton::arch::x86::ID_INS_FRNDINT;
            break;

          case X86_INS_FRSTOR:
            tritonId = triton::arch::x86::ID_INS_FRSTOR;
            break;

          case X86_INS_FNSAVE:
            tritonId = triton::arch::x86::ID_INS_FNSAVE;
            break;

          case X86_INS_FSCALE:
            tritonId = triton::arch::x86::ID_INS_FSCALE;
            break;

          case X86_INS_FSETPM:
            tritonId = triton::arch::x86::ID_INS_FSETPM;
            break;

          case X86_INS_FSINCOS:
            tritonId = triton::arch::x86::ID_INS_FSINCOS;
            break;

          case X86_INS_FNSTENV:
            tritonId = triton::arch::x86::ID_INS_FNSTENV;
            break;

          case X86_INS_FXAM:
            tritonId = triton::arch::x86::ID_INS_FXAM;
            break;

          case X86_INS_FXRSTOR:
            tritonId = triton::arch::x86::ID_INS_FXRSTOR;
            break;

          case X86_INS_FXRSTOR64:
            tritonId = triton::arch::x86::ID_INS_FXRSTOR64;
            break;

          case X86_INS_FXSAVE:
            tritonId = triton::arch::x86::ID_INS_FXSAVE;
            break;

          case X86_INS_FXSAVE64:
            tritonId = triton::arch::x86::ID_INS_FXSAVE64;
            break;

          case X86_INS_FXTRACT:
            tritonId = triton::arch::x86::ID_INS_FXTRACT;
            break;

          case X86_INS_FYL2X:
            tritonId = triton::arch::x86::ID_INS_FYL2X;
            break;

          case X86_INS_FYL2XP1:
            tritonId = triton::arch::x86::ID_INS_FYL2XP1;
            break;

          case X86_INS_MOVAPD:
            tritonId = triton::arch::x86::ID_INS_MOVAPD;
            break;

          case X86_INS_MOVAPS:
            tritonId = triton::arch::x86::ID_INS_MOVAPS;
            break;

          case X86_INS_ORPD:
            tritonId = triton::arch::x86::ID_INS_ORPD;
            break;

          case X86_INS_ORPS:
            tritonId = triton::arch::x86::ID_INS_ORPS;
            break;

          case X86_INS_VMOVAPD:
            tritonId = triton::arch::x86::ID_INS_VMOVAPD;
            break;

          case X86_INS_VMOVAPS:
            tritonId = triton::arch::x86::ID_INS_VMOVAPS;
            break;

          case X86_INS_XORPD:
            tritonId = triton::arch::x86::ID_INS_XORPD;
            break;

          case X86_INS_XORPS:
            tritonId = triton::arch::x86::ID_INS_XORPS;
            break;

          case X86_INS_GETSEC:
            tritonId = triton::arch::x86::ID_INS_GETSEC;
            break;

          case X86_INS_HADDPD:
            tritonId = triton::arch::x86::ID_INS_HADDPD;
            break;

          case X86_INS_HADDPS:
            tritonId = triton::arch::x86::ID_INS_HADDPS;
            break;

          case X86_INS_HLT:
            tritonId = triton::arch::x86::ID_INS_HLT;
            break;

          case X86_INS_HSUBPD:
            tritonId = triton::arch::x86::ID_INS_HSUBPD;
            break;

          case X86_INS_HSUBPS:
            tritonId = triton::arch::x86::ID_INS_HSUBPS;
            break;

          case X86_INS_IDIV:
            tritonId = triton::arch::x86::ID_INS_IDIV;
            break;

          case X86_INS_FILD:
            tritonId = triton::arch::x86::ID_INS_FILD;
            break;

          case X86_INS_IMUL:
            tritonId = triton::arch::x86::ID_INS_IMUL;
            break;

          case X86_INS_IN:
            tritonId = triton::arch::x86::ID_INS_IN;
            break;

          case X86_INS_INC:
            tritonId = triton::arch::x86::ID_INS_INC;
            break;

          case X86_INS_INSB:
            tritonId = triton::arch::x86::ID_INS_INSB;
            break;

          case X86_INS_INSERTPS:
            tritonId = triton::arch::x86::ID_INS_INSERTPS;
            break;

          case X86_INS_INSERTQ:
            tritonId = triton::arch::x86::ID_INS_INSERTQ;
            break;

          case X86_INS_INSD:
            tritonId = triton::arch::x86::ID_INS_INSD;
            break;

          case X86_INS_INSW:
            tritonId = triton::arch::x86::ID_INS_INSW;
            break;

          case X86_INS_INT:
            tritonId = triton::arch::x86::ID_INS_INT;
            break;

          case X86_INS_INT1:
            tritonId = triton::arch::x86::ID_INS_INT1;
            break;

          case X86_INS_INT3:
            tritonId = triton::arch::x86::ID_INS_INT3;
            break;

          case X86_INS_INTO:
            tritonId = triton::arch::x86::ID_INS_INTO;
            break;

          case X86_INS_INVD:
            tritonId = triton::arch::x86::ID_INS_INVD;
            break;

          case X86_INS_INVEPT:
            tritonId = triton::arch::x86::ID_INS_INVEPT;
            break;

          case X86_INS_INVLPG:
            tritonId = triton::arch::x86::ID_INS_INVLPG;
            break;

          case X86_INS_INVLPGA:
            tritonId = triton::arch::x86::ID_INS_INVLPGA;
            break;

          case X86_INS_INVPCID:
            tritonId = triton::arch::x86::ID_INS_INVPCID;
            break;

          case X86_INS_INVVPID:
            tritonId = triton::arch::x86::ID_INS_INVVPID;
            break;

          case X86_INS_IRET:
            tritonId = triton::arch::x86::ID_INS_IRET;
            break;

          case X86_INS_IRETD:
            tritonId = triton::arch::x86::ID_INS_IRETD;
            break;

          case X86_INS_IRETQ:
            tritonId = triton::arch::x86::ID_INS_IRETQ;
            break;

          case X86_INS_FISTTP:
            tritonId = triton::arch::x86::ID_INS_FISTTP;
            break;

          case X86_INS_FIST:
            tritonId = triton::arch::x86::ID_INS_FIST;
            break;

          case X86_INS_FISTP:
            tritonId = triton::arch::x86::ID_INS_FISTP;
            break;

          case X86_INS_UCOMISD:
            tritonId = triton::arch::x86::ID_INS_UCOMISD;
            break;

          case X86_INS_UCOMISS:
            tritonId = triton::arch::x86::ID_INS_UCOMISS;
            break;

          case X86_INS_VCMP:
            tritonId = triton::arch::x86::ID_INS_VCMP;
            break;

          case X86_INS_VCOMISD:
            tritonId = triton::arch::x86::ID_INS_VCOMISD;
            break;

          case X86_INS_VCOMISS:
            tritonId = triton::arch::x86::ID_INS_VCOMISS;
            break;

          case X86_INS_VCVTSD2SS:
            tritonId = triton::arch::x86::ID_INS_VCVTSD2SS;
            break;

          case X86_INS_VCVTSI2SD:
            tritonId = triton::arch::x86::ID_INS_VCVTSI2SD;
            break;

          case X86_INS_VCVTSI2SS:
            tritonId = triton::arch::x86::ID_INS_VCVTSI2SS;
            break;

          case X86_INS_VCVTSS2SD:
            tritonId = triton::arch::x86::ID_INS_VCVTSS2SD;
            break;

          case X86_INS_VCVTTSD2SI:
            tritonId = triton::arch::x86::ID_INS_VCVTTSD2SI;
            break;

          case X86_INS_VCVTTSD2USI:
            tritonId = triton::arch::x86::ID_INS_VCVTTSD2USI;
            break;

          case X86_INS_VCVTTSS2SI:
            tritonId = triton::arch::x86::ID_INS_VCVTTSS2SI;
            break;

          case X86_INS_VCVTTSS2USI:
            tritonId = triton::arch::x86::ID_INS_VCVTTSS2USI;
            break;

          case X86_INS_VCVTUSI2SD:
            tritonId = triton::arch::x86::ID_INS_VCVTUSI2SD;
            break;

          case X86_INS_VCVTUSI2SS:
            tritonId = triton::arch::x86::ID_INS_VCVTUSI2SS;
            break;

          case X86_INS_VUCOMISD:
            tritonId = triton::arch::x86::ID_INS_VUCOMISD;
            break;

          case X86_INS_VUCOMISS:
            tritonId = triton::arch::x86::ID_INS_VUCOMISS;
            break;

          case X86_INS_JAE:
            tritonId = triton::arch::x86::ID_INS_JAE;
            break;

          case X86_INS_JA:
            tritonId = triton::arch::x86::ID_INS_JA;
            break;

          case X86_INS_JBE:
            tritonId = triton::arch::x86::ID_INS_JBE;
            break;

          case X86_INS_JB:
            tritonId = triton::arch::x86::ID_INS_JB;
            break;

          case X86_INS_JCXZ:
            tritonId = triton::arch::x86::ID_INS_JCXZ;
            break;

          case X86_INS_JECXZ:
            tritonId = triton::arch::x86::ID_INS_JECXZ;
            break;

          case X86_INS_JE:
            tritonId = triton::arch::x86::ID_INS_JE;
            break;

          case X86_INS_JGE:
            tritonId = triton::arch::x86::ID_INS_JGE;
            break;

          case X86_INS_JG:
            tritonId = triton::arch::x86::ID_INS_JG;
            break;

          case X86_INS_JLE:
            tritonId = triton::arch::x86::ID_INS_JLE;
            break;

          case X86_INS_JL:
            tritonId = triton::arch::x86::ID_INS_JL;
            break;

          case X86_INS_JMP:
            tritonId = triton::arch::x86::ID_INS_JMP;
            break;

          case X86_INS_JNE:
            tritonId = triton::arch::x86::ID_INS_JNE;
            break;

          case X86_INS_JNO:
            tritonId = triton::arch::x86::ID_INS_JNO;
            break;

          case X86_INS_JNP:
            tritonId = triton::arch::x86::ID_INS_JNP;
            break;

          case X86_INS_JNS:
            tritonId = triton::arch::x86::ID_INS_JNS;
            break;

          case X86_INS_JO:
            tritonId = triton::arch::x86::ID_INS_JO;
            break;

          case X86_INS_JP:
            tritonId = triton::arch::x86::ID_INS_JP;
            break;

          case X86_INS_JRCXZ:
            tritonId = triton::arch::x86::ID_INS_JRCXZ;
            break;

          case X86_INS_JS:
            tritonId = triton::arch::x86::ID_INS_JS;
            break;

          case X86_INS_KANDB:
            tritonId = triton::arch::x86::ID_INS_KANDB;
            break;

          case X86_INS_KANDD:
            tritonId = triton::arch::x86::ID_INS_KANDD;
            break;

          case X86_INS_KANDNB:
            tritonId = triton::arch::x86::ID_INS_KANDNB;
            break;

          case X86_INS_KANDND:
            tritonId = triton::arch::x86::ID_INS_KANDND;
            break;

          case X86_INS_KANDNQ:
            tritonId = triton::arch::x86::ID_INS_KANDNQ;
            break;

          case X86_INS_KANDNW:
            tritonId = triton::arch::x86::ID_INS_KANDNW;
            break;

          case X86_INS_KANDQ:
            tritonId = triton::arch::x86::ID_INS_KANDQ;
            break;

          case X86_INS_KANDW:
            tritonId = triton::arch::x86::ID_INS_KANDW;
            break;

          case X86_INS_KMOVB:
            tritonId = triton::arch::x86::ID_INS_KMOVB;
            break;

          case X86_INS_KMOVD:
            tritonId = triton::arch::x86::ID_INS_KMOVD;
            break;

          case X86_INS_KMOVQ:
            tritonId = triton::arch::x86::ID_INS_KMOVQ;
            break;

          case X86_INS_KMOVW:
            tritonId = triton::arch::x86::ID_INS_KMOVW;
            break;

          case X86_INS_KNOTB:
            tritonId = triton::arch::x86::ID_INS_KNOTB;
            break;

          case X86_INS_KNOTD:
            tritonId = triton::arch::x86::ID_INS_KNOTD;
            break;

          case X86_INS_KNOTQ:
            tritonId = triton::arch::x86::ID_INS_KNOTQ;
            break;

          case X86_INS_KNOTW:
            tritonId = triton::arch::x86::ID_INS_KNOTW;
            break;

          case X86_INS_KORB:
            tritonId = triton::arch::x86::ID_INS_KORB;
            break;

          case X86_INS_KORD:
            tritonId = triton::arch::x86::ID_INS_KORD;
            break;

          case X86_INS_KORQ:
            tritonId = triton::arch::x86::ID_INS_KORQ;
            break;

          case X86_INS_KORTESTW:
            tritonId = triton::arch::x86::ID_INS_KORTESTW;
            break;

          case X86_INS_KORW:
            tritonId = triton::arch::x86::ID_INS_KORW;
            break;

          case X86_INS_KSHIFTLW:
            tritonId = triton::arch::x86::ID_INS_KSHIFTLW;
            break;

          case X86_INS_KSHIFTRW:
            tritonId = triton::arch::x86::ID_INS_KSHIFTRW;
            break;

          case X86_INS_KUNPCKBW:
            tritonId = triton::arch::x86::ID_INS_KUNPCKBW;
            break;

          case X86_INS_KXNORB:
            tritonId = triton::arch::x86::ID_INS_KXNORB;
            break;

          case X86_INS_KXNORD:
            tritonId = triton::arch::x86::ID_INS_KXNORD;
            break;

          case X86_INS_KXNORQ:
            tritonId = triton::arch::x86::ID_INS_KXNORQ;
            break;

          case X86_INS_KXNORW:
            tritonId = triton::arch::x86::ID_INS_KXNORW;
            break;

          case X86_INS_KXORB:
            tritonId = triton::arch::x86::ID_INS_KXORB;
            break;

          case X86_INS_KXORD:
            tritonId = triton::arch::x86::ID_INS_KXORD;
            break;

          case X86_INS_KXORQ:
            tritonId = triton::arch::x86::ID_INS_KXORQ;
            break;

          case X86_INS_KXORW:
            tritonId = triton::arch::x86::ID_INS_KXORW;
            break;

          case X86_INS_LAHF:
            tritonId = triton::arch::x86::ID_INS_LAHF;
            break;

          case X86_INS_LAR:
            tritonId = triton::arch::x86::ID_INS_LAR;
            break;

          case X86_INS_LDDQU:
            tritonId = triton::arch::x86::ID_INS_LDDQU;
            break;

          case X86_INS_LDMXCSR:
            tritonId = triton::arch::x86::ID_INS_LDMXCSR;
            break;

          case X86_INS_LDS:
            tritonId = triton::arch::x86::ID_INS_LDS;
            break;

          case X86_INS_FLDZ:
            tritonId = triton::arch::x86::ID_INS_FLDZ;
            break;

          case X86_INS_FLD1:
            tritonId = triton::arch::x86::ID_INS_FLD1;
            break;

          case X86_INS_FLD:
            tritonId = triton::arch::x86::ID_INS_FLD;
            break;

          case X86_INS_LEA:
            tritonId = triton::arch::x86::ID_INS_LEA;
            break;

          case X86_INS_LEAVE:
            tritonId = triton::arch::x86::ID_INS_LEAVE;
            break;

          case X86_INS_LES:
            tritonId = triton::arch::x86::ID_INS_LES;
            break;

          case X86_INS_LFENCE:
            tritonId = triton::arch::x86::ID_INS_LFENCE;
            break;

          case X86_INS_LFS:
            tritonId = triton::arch::x86::ID_INS_LFS;
            break;

          case X86_INS_LGDT:
            tritonId = triton::arch::x86::ID_INS_LGDT;
            break;

          case X86_INS_LGS:
            tritonId = triton::arch::x86::ID_INS_LGS;
            break;

          case X86_INS_LIDT:
            tritonId = triton::arch::x86::ID_INS_LIDT;
            break;

          case X86_INS_LLDT:
            tritonId = triton::arch::x86::ID_INS_LLDT;
            break;

          case X86_INS_LMSW:
            tritonId = triton::arch::x86::ID_INS_LMSW;
            break;

          case X86_INS_OR:
            tritonId = triton::arch::x86::ID_INS_OR;
            break;

          case X86_INS_SUB:
            tritonId = triton::arch::x86::ID_INS_SUB;
            break;

          case X86_INS_XOR:
            tritonId = triton::arch::x86::ID_INS_XOR;
            break;

          case X86_INS_LODSB:
            tritonId = triton::arch::x86::ID_INS_LODSB;
            break;

          case X86_INS_LODSD:
            tritonId = triton::arch::x86::ID_INS_LODSD;
            break;

          case X86_INS_LODSQ:
            tritonId = triton::arch::x86::ID_INS_LODSQ;
            break;

          case X86_INS_LODSW:
            tritonId = triton::arch::x86::ID_INS_LODSW;
            break;

          case X86_INS_LOOP:
            tritonId = triton::arch::x86::ID_INS_LOOP;
            break;

          case X86_INS_LOOPE:
            tritonId = triton::arch::x86::ID_INS_LOOPE;
            break;

          case X86_INS_LOOPNE:
            tritonId = triton::arch::x86::ID_INS_LOOPNE;
            break;

          case X86_INS_RETF:
            tritonId = triton::arch::x86::ID_INS_RETF;
            break;

          case X86_INS_RETFQ:
            tritonId = triton::arch::x86::ID_INS_RETFQ;
            break;

          case X86_INS_LSL:
            tritonId = triton::arch::x86::ID_INS_LSL;
            break;

          case X86_INS_LSS:
            tritonId = triton::arch::x86::ID_INS_LSS;
            break;

          case X86_INS_LTR:
            tritonId = triton::arch::x86::ID_INS_LTR;
            break;

          case X86_INS_XADD:
            tritonId = triton::arch::x86::ID_INS_XADD;
            break;

          case X86_INS_LZCNT:
            tritonId = triton::arch::x86::ID_INS_LZCNT;
            break;

          case X86_INS_MASKMOVDQU:
            tritonId = triton::arch::x86::ID_INS_MASKMOVDQU;
            break;

          case X86_INS_MAXPD:
            tritonId = triton::arch::x86::ID_INS_MAXPD;
            break;

          case X86_INS_MAXPS:
            tritonId = triton::arch::x86::ID_INS_MAXPS;
            break;

          case X86_INS_MAXSD:
            tritonId = triton::arch::x86::ID_INS_MAXSD;
            break;

          case X86_INS_MAXSS:
            tritonId = triton::arch::x86::ID_INS_MAXSS;
            break;

          case X86_INS_MFENCE:
            tritonId = triton::arch::x86::ID_INS_MFENCE;
            break;

          case X86_INS_MINPD:
            tritonId = triton::arch::x86::ID_INS_MINPD;
            break;

          case X86_INS_MINPS:
            tritonId = triton::arch::x86::ID_INS_MINPS;
            break;

          case X86_INS_MINSD:
            tritonId = triton::arch::x86::ID_INS_MINSD;
            break;

          case X86_INS_MINSS:
            tritonId = triton::arch::x86::ID_INS_MINSS;
            break;

          case X86_INS_CVTPD2PI:
            tritonId = triton::arch::x86::ID_INS_CVTPD2PI;
            break;

          case X86_INS_CVTPI2PD:
            tritonId = triton::arch::x86::ID_INS_CVTPI2PD;
            break;

          case X86_INS_CVTPI2PS:
            tritonId = triton::arch::x86::ID_INS_CVTPI2PS;
            break;

          case X86_INS_CVTPS2PI:
            tritonId = triton::arch::x86::ID_INS_CVTPS2PI;
            break;

          case X86_INS_CVTTPD2PI:
            tritonId = triton::arch::x86::ID_INS_CVTTPD2PI;
            break;

          case X86_INS_CVTTPS2PI:
            tritonId = triton::arch::x86::ID_INS_CVTTPS2PI;
            break;

          case X86_INS_EMMS:
            tritonId = triton::arch::x86::ID_INS_EMMS;
            break;

          case X86_INS_MASKMOVQ:
            tritonId = triton::arch::x86::ID_INS_MASKMOVQ;
            break;

          case X86_INS_MOVD:
            tritonId = triton::arch::x86::ID_INS_MOVD;
            break;

          case X86_INS_MOVDQ2Q:
            tritonId = triton::arch::x86::ID_INS_MOVDQ2Q;
            break;

          case X86_INS_MOVNTQ:
            tritonId = triton::arch::x86::ID_INS_MOVNTQ;
            break;

          case X86_INS_MOVQ2DQ:
            tritonId = triton::arch::x86::ID_INS_MOVQ2DQ;
            break;

          case X86_INS_MOVQ:
            tritonId = triton::arch::x86::ID_INS_MOVQ;
            break;

          case X86_INS_PABSB:
            tritonId = triton::arch::x86::ID_INS_PABSB;
            break;

          case X86_INS_PABSD:
            tritonId = triton::arch::x86::ID_INS_PABSD;
            break;

          case X86_INS_PABSW:
            tritonId = triton::arch::x86::ID_INS_PABSW;
            break;

          case X86_INS_PACKSSDW:
            tritonId = triton::arch::x86::ID_INS_PACKSSDW;
            break;

          case X86_INS_PACKSSWB:
            tritonId = triton::arch::x86::ID_INS_PACKSSWB;
            break;

          case X86_INS_PACKUSWB:
            tritonId = triton::arch::x86::ID_INS_PACKUSWB;
            break;

          case X86_INS_PADDB:
            tritonId = triton::arch::x86::ID_INS_PADDB;
            break;

          case X86_INS_PADDD:
            tritonId = triton::arch::x86::ID_INS_PADDD;
            break;

          case X86_INS_PADDQ:
            tritonId = triton::arch::x86::ID_INS_PADDQ;
            break;

          case X86_INS_PADDSB:
            tritonId = triton::arch::x86::ID_INS_PADDSB;
            break;

          case X86_INS_PADDSW:
            tritonId = triton::arch::x86::ID_INS_PADDSW;
            break;

          case X86_INS_PADDUSB:
            tritonId = triton::arch::x86::ID_INS_PADDUSB;
            break;

          case X86_INS_PADDUSW:
            tritonId = triton::arch::x86::ID_INS_PADDUSW;
            break;

          case X86_INS_PADDW:
            tritonId = triton::arch::x86::ID_INS_PADDW;
            break;

          case X86_INS_PALIGNR:
            tritonId = triton::arch::x86::ID_INS_PALIGNR;
            break;

          case X86_INS_PANDN:
            tritonId = triton::arch::x86::ID_INS_PANDN;
            break;

          case X86_INS_PAND:
            tritonId = triton::arch::x86::ID_INS_PAND;
            break;

          case X86_INS_PAVGB:
            tritonId = triton::arch::x86::ID_INS_PAVGB;
            break;

          case X86_INS_PAVGW:
            tritonId = triton::arch::x86::ID_INS_PAVGW;
            break;

          case X86_INS_PCMPEQB:
            tritonId = triton::arch::x86::ID_INS_PCMPEQB;
            break;

          case X86_INS_PCMPEQD:
            tritonId = triton::arch::x86::ID_INS_PCMPEQD;
            break;

          case X86_INS_PCMPEQW:
            tritonId = triton::arch::x86::ID_INS_PCMPEQW;
            break;

          case X86_INS_PCMPGTB:
            tritonId = triton::arch::x86::ID_INS_PCMPGTB;
            break;

          case X86_INS_PCMPGTD:
            tritonId = triton::arch::x86::ID_INS_PCMPGTD;
            break;

          case X86_INS_PCMPGTW:
            tritonId = triton::arch::x86::ID_INS_PCMPGTW;
            break;

          case X86_INS_PEXTRW:
            tritonId = triton::arch::x86::ID_INS_PEXTRW;
            break;

          case X86_INS_PHADDSW:
            tritonId = triton::arch::x86::ID_INS_PHADDSW;
            break;

          case X86_INS_PHADDW:
            tritonId = triton::arch::x86::ID_INS_PHADDW;
            break;

          case X86_INS_PHADDD:
            tritonId = triton::arch::x86::ID_INS_PHADDD;
            break;

          case X86_INS_PHSUBD:
            tritonId = triton::arch::x86::ID_INS_PHSUBD;
            break;

          case X86_INS_PHSUBSW:
            tritonId = triton::arch::x86::ID_INS_PHSUBSW;
            break;

          case X86_INS_PHSUBW:
            tritonId = triton::arch::x86::ID_INS_PHSUBW;
            break;

          case X86_INS_PINSRW:
            tritonId = triton::arch::x86::ID_INS_PINSRW;
            break;

          case X86_INS_PMADDUBSW:
            tritonId = triton::arch::x86::ID_INS_PMADDUBSW;
            break;

          case X86_INS_PMADDWD:
            tritonId = triton::arch::x86::ID_INS_PMADDWD;
            break;

          case X86_INS_PMAXSW:
            tritonId = triton::arch::x86::ID_INS_PMAXSW;
            break;

          case X86_INS_PMAXUB:
            tritonId = triton::arch::x86::ID_INS_PMAXUB;
            break;

          case X86_INS_PMINSW:
            tritonId = triton::arch::x86::ID_INS_PMINSW;
            break;

          case X86_INS_PMINUB:
            tritonId = triton::arch::x86::ID_INS_PMINUB;
            break;

          case X86_INS_PMOVMSKB:
            tritonId = triton::arch::x86::ID_INS_PMOVMSKB;
            break;

          case X86_INS_PMULHRSW:
            tritonId = triton::arch::x86::ID_INS_PMULHRSW;
            break;

          case X86_INS_PMULHUW:
            tritonId = triton::arch::x86::ID_INS_PMULHUW;
            break;

          case X86_INS_PMULHW:
            tritonId = triton::arch::x86::ID_INS_PMULHW;
            break;

          case X86_INS_PMULLW:
            tritonId = triton::arch::x86::ID_INS_PMULLW;
            break;

          case X86_INS_PMULUDQ:
            tritonId = triton::arch::x86::ID_INS_PMULUDQ;
            break;

          case X86_INS_POR:
            tritonId = triton::arch::x86::ID_INS_POR;
            break;

          case X86_INS_PSADBW:
            tritonId = triton::arch::x86::ID_INS_PSADBW;
            break;

          case X86_INS_PSHUFB:
            tritonId = triton::arch::x86::ID_INS_PSHUFB;
            break;

          case X86_INS_PSHUFW:
            tritonId = triton::arch::x86::ID_INS_PSHUFW;
            break;

          case X86_INS_PSIGNB:
            tritonId = triton::arch::x86::ID_INS_PSIGNB;
            break;

          case X86_INS_PSIGND:
            tritonId = triton::arch::x86::ID_INS_PSIGND;
            break;

          case X86_INS_PSIGNW:
            tritonId = triton::arch::x86::ID_INS_PSIGNW;
            break;

          case X86_INS_PSLLD:
            tritonId = triton::arch::x86::ID_INS_PSLLD;
            break;

          case X86_INS_PSLLQ:
            tritonId = triton::arch::x86::ID_INS_PSLLQ;
            break;

          case X86_INS_PSLLW:
            tritonId = triton::arch::x86::ID_INS_PSLLW;
            break;

          case X86_INS_PSRAD:
            tritonId = triton::arch::x86::ID_INS_PSRAD;
            break;

          case X86_INS_PSRAW:
            tritonId = triton::arch::x86::ID_INS_PSRAW;
            break;

          case X86_INS_PSRLD:
            tritonId = triton::arch::x86::ID_INS_PSRLD;
            break;

          case X86_INS_PSRLQ:
            tritonId = triton::arch::x86::ID_INS_PSRLQ;
            break;

          case X86_INS_PSRLW:
            tritonId = triton::arch::x86::ID_INS_PSRLW;
            break;

          case X86_INS_PSUBB:
            tritonId = triton::arch::x86::ID_INS_PSUBB;
            break;

          case X86_INS_PSUBD:
            tritonId = triton::arch::x86::ID_INS_PSUBD;
            break;

          case X86_INS_PSUBQ:
            tritonId = triton::arch::x86::ID_INS_PSUBQ;
            break;

          case X86_INS_PSUBSB:
            tritonId = triton::arch::x86::ID_INS_PSUBSB;
            break;

          case X86_INS_PSUBSW:
            tritonId = triton::arch::x86::ID_INS_PSUBSW;
            break;

          case X86_INS_PSUBUSB:
            tritonId = triton::arch::x86::ID_INS_PSUBUSB;
            break;

          case X86_INS_PSUBUSW:
            tritonId = triton::arch::x86::ID_INS_PSUBUSW;
            break;

          case X86_INS_PSUBW:
            tritonId = triton::arch::x86::ID_INS_PSUBW;
            break;

          case X86_INS_PUNPCKHBW:
            tritonId = triton::arch::x86::ID_INS_PUNPCKHBW;
            break;

          case X86_INS_PUNPCKHDQ:
            tritonId = triton::arch::x86::ID_INS_PUNPCKHDQ;
            break;

          case X86_INS_PUNPCKHWD:
            tritonId = triton::arch::x86::ID_INS_PUNPCKHWD;
            break;

          case X86_INS_PUNPCKLBW:
            tritonId = triton::arch::x86::ID_INS_PUNPCKLBW;
            break;

          case X86_INS_PUNPCKLDQ:
            tritonId = triton::arch::x86::ID_INS_PUNPCKLDQ;
            break;

          case X86_INS_PUNPCKLWD:
            tritonId = triton::arch::x86::ID_INS_PUNPCKLWD;
            break;

          case X86_INS_PXOR:
            tritonId = triton::arch::x86::ID_INS_PXOR;
            break;

          case X86_INS_MONITOR:
            tritonId = triton::arch::x86::ID_INS_MONITOR;
            break;

          case X86_INS_MONTMUL:
            tritonId = triton::arch::x86::ID_INS_MONTMUL;
            break;

          case X86_INS_MOV:
            tritonId = triton::arch::x86::ID_INS_MOV;
            break;

          case X86_INS_MOVABS:
            tritonId = triton::arch::x86::ID_INS_MOVABS;
            break;

          case X86_INS_MOVBE:
            tritonId = triton::arch::x86::ID_INS_MOVBE;
            break;

          case X86_INS_MOVDDUP:
            tritonId = triton::arch::x86::ID_INS_MOVDDUP;
            break;

          case X86_INS_MOVDQA:
            tritonId = triton::arch::x86::ID_INS_MOVDQA;
            break;

          case X86_INS_MOVDQU:
            tritonId = triton::arch::x86::ID_INS_MOVDQU;
            break;

          case X86_INS_MOVHLPS:
            tritonId = triton::arch::x86::ID_INS_MOVHLPS;
            break;

          case X86_INS_MOVHPD:
            tritonId = triton::arch::x86::ID_INS_MOVHPD;
            break;

          case X86_INS_MOVHPS:
            tritonId = triton::arch::x86::ID_INS_MOVHPS;
            break;

          case X86_INS_MOVLHPS:
            tritonId = triton::arch::x86::ID_INS_MOVLHPS;
            break;

          case X86_INS_MOVLPD:
            tritonId = triton::arch::x86::ID_INS_MOVLPD;
            break;

          case X86_INS_MOVLPS:
            tritonId = triton::arch::x86::ID_INS_MOVLPS;
            break;

          case X86_INS_MOVMSKPD:
            tritonId = triton::arch::x86::ID_INS_MOVMSKPD;
            break;

          case X86_INS_MOVMSKPS:
            tritonId = triton::arch::x86::ID_INS_MOVMSKPS;
            break;

          case X86_INS_MOVNTDQA:
            tritonId = triton::arch::x86::ID_INS_MOVNTDQA;
            break;

          case X86_INS_MOVNTDQ:
            tritonId = triton::arch::x86::ID_INS_MOVNTDQ;
            break;

          case X86_INS_MOVNTI:
            tritonId = triton::arch::x86::ID_INS_MOVNTI;
            break;

          case X86_INS_MOVNTPD:
            tritonId = triton::arch::x86::ID_INS_MOVNTPD;
            break;

          case X86_INS_MOVNTPS:
            tritonId = triton::arch::x86::ID_INS_MOVNTPS;
            break;

          case X86_INS_MOVNTSD:
            tritonId = triton::arch::x86::ID_INS_MOVNTSD;
            break;

          case X86_INS_MOVNTSS:
            tritonId = triton::arch::x86::ID_INS_MOVNTSS;
            break;

          case X86_INS_MOVSB:
            tritonId = triton::arch::x86::ID_INS_MOVSB;
            break;

          case X86_INS_MOVSD:
            tritonId = triton::arch::x86::ID_INS_MOVSD;
            break;

          case X86_INS_MOVSHDUP:
            tritonId = triton::arch::x86::ID_INS_MOVSHDUP;
            break;

          case X86_INS_MOVSLDUP:
            tritonId = triton::arch::x86::ID_INS_MOVSLDUP;
            break;

          case X86_INS_MOVSQ:
            tritonId = triton::arch::x86::ID_INS_MOVSQ;
            break;

          case X86_INS_MOVSS:
            tritonId = triton::arch::x86::ID_INS_MOVSS;
            break;

          case X86_INS_MOVSW:
            tritonId = triton::arch::x86::ID_INS_MOVSW;
            break;

          case X86_INS_MOVSX:
            tritonId = triton::arch::x86::ID_INS_MOVSX;
            break;

          case X86_INS_MOVSXD:
            tritonId = triton::arch::x86::ID_INS_MOVSXD;
            break;

          case X86_INS_MOVUPD:
            tritonId = triton::arch::x86::ID_INS_MOVUPD;
            break;

          case X86_INS_MOVUPS:
            tritonId = triton::arch::x86::ID_INS_MOVUPS;
            break;

          case X86_INS_MOVZX:
            tritonId = triton::arch::x86::ID_INS_MOVZX;
            break;

          case X86_INS_MPSADBW:
            tritonId = triton::arch::x86::ID_INS_MPSADBW;
            break;

          case X86_INS_MUL:
            tritonId = triton::arch::x86::ID_INS_MUL;
            break;

          case X86_INS_MULPD:
            tritonId = triton::arch::x86::ID_INS_MULPD;
            break;

          case X86_INS_MULPS:
            tritonId = triton::arch::x86::ID_INS_MULPS;
            break;

          case X86_INS_MULSD:
            tritonId = triton::arch::x86::ID_INS_MULSD;
            break;

          case X86_INS_MULSS:
            tritonId = triton::arch::x86::ID_INS_MULSS;
            break;

          case X86_INS_MULX:
            tritonId = triton::arch::x86::ID_INS_MULX;
            break;

          case X86_INS_FMUL:
            tritonId = triton::arch::x86::ID_INS_FMUL;
            break;

          case X86_INS_FIMUL:
            tritonId = triton::arch::x86::ID_INS_FIMUL;
            break;

          case X86_INS_FMULP:
            tritonId = triton::arch::x86::ID_INS_FMULP;
            break;

          case X86_INS_MWAIT:
            tritonId = triton::arch::x86::ID_INS_MWAIT;
            break;

          case X86_INS_NEG:
            tritonId = triton::arch::x86::ID_INS_NEG;
            break;

          case X86_INS_NOP:
            tritonId = triton::arch::x86::ID_INS_NOP;
            break;

          case X86_INS_NOT:
            tritonId = triton::arch::x86::ID_INS_NOT;
            break;

          case X86_INS_OUT:
            tritonId = triton::arch::x86::ID_INS_OUT;
            break;

          case X86_INS_OUTSB:
            tritonId = triton::arch::x86::ID_INS_OUTSB;
            break;

          case X86_INS_OUTSD:
            tritonId = triton::arch::x86::ID_INS_OUTSD;
            break;

          case X86_INS_OUTSW:
            tritonId = triton::arch::x86::ID_INS_OUTSW;
            break;

          case X86_INS_PACKUSDW:
            tritonId = triton::arch::x86::ID_INS_PACKUSDW;
            break;

          case X86_INS_PAUSE:
            tritonId = triton::arch::x86::ID_INS_PAUSE;
            break;

          case X86_INS_PAVGUSB:
            tritonId = triton::arch::x86::ID_INS_PAVGUSB;
            break;

          case X86_INS_PBLENDVB:
            tritonId = triton::arch::x86::ID_INS_PBLENDVB;
            break;

          case X86_INS_PBLENDW:
            tritonId = triton::arch::x86::ID_INS_PBLENDW;
            break;

          case X86_INS_PCLMULQDQ:
            tritonId = triton::arch::x86::ID_INS_PCLMULQDQ;
            break;

          case X86_INS_PCMPEQQ:
            tritonId = triton::arch::x86::ID_INS_PCMPEQQ;
            break;

          case X86_INS_PCMPESTRI:
            tritonId = triton::arch::x86::ID_INS_PCMPESTRI;
            break;

          case X86_INS_PCMPESTRM:
            tritonId = triton::arch::x86::ID_INS_PCMPESTRM;
            break;

          case X86_INS_PCMPGTQ:
            tritonId = triton::arch::x86::ID_INS_PCMPGTQ;
            break;

          case X86_INS_PCMPISTRI:
            tritonId = triton::arch::x86::ID_INS_PCMPISTRI;
            break;

          case X86_INS_PCMPISTRM:
            tritonId = triton::arch::x86::ID_INS_PCMPISTRM;
            break;

          case X86_INS_PDEP:
            tritonId = triton::arch::x86::ID_INS_PDEP;
            break;

          case X86_INS_PEXT:
            tritonId = triton::arch::x86::ID_INS_PEXT;
            break;

          case X86_INS_PEXTRB:
            tritonId = triton::arch::x86::ID_INS_PEXTRB;
            break;

          case X86_INS_PEXTRD:
            tritonId = triton::arch::x86::ID_INS_PEXTRD;
            break;

          case X86_INS_PEXTRQ:
            tritonId = triton::arch::x86::ID_INS_PEXTRQ;
            break;

          case X86_INS_PF2ID:
            tritonId = triton::arch::x86::ID_INS_PF2ID;
            break;

          case X86_INS_PF2IW:
            tritonId = triton::arch::x86::ID_INS_PF2IW;
            break;

          case X86_INS_PFACC:
            tritonId = triton::arch::x86::ID_INS_PFACC;
            break;

          case X86_INS_PFADD:
            tritonId = triton::arch::x86::ID_INS_PFADD;
            break;

          case X86_INS_PFCMPEQ:
            tritonId = triton::arch::x86::ID_INS_PFCMPEQ;
            break;

          case X86_INS_PFCMPGE:
            tritonId = triton::arch::x86::ID_INS_PFCMPGE;
            break;

          case X86_INS_PFCMPGT:
            tritonId = triton::arch::x86::ID_INS_PFCMPGT;
            break;

          case X86_INS_PFMAX:
            tritonId = triton::arch::x86::ID_INS_PFMAX;
            break;

          case X86_INS_PFMIN:
            tritonId = triton::arch::x86::ID_INS_PFMIN;
            break;

          case X86_INS_PFMUL:
            tritonId = triton::arch::x86::ID_INS_PFMUL;
            break;

          case X86_INS_PFNACC:
            tritonId = triton::arch::x86::ID_INS_PFNACC;
            break;

          case X86_INS_PFPNACC:
            tritonId = triton::arch::x86::ID_INS_PFPNACC;
            break;

          case X86_INS_PFRCPIT1:
            tritonId = triton::arch::x86::ID_INS_PFRCPIT1;
            break;

          case X86_INS_PFRCPIT2:
            tritonId = triton::arch::x86::ID_INS_PFRCPIT2;
            break;

          case X86_INS_PFRCP:
            tritonId = triton::arch::x86::ID_INS_PFRCP;
            break;

          case X86_INS_PFRSQIT1:
            tritonId = triton::arch::x86::ID_INS_PFRSQIT1;
            break;

          case X86_INS_PFRSQRT:
            tritonId = triton::arch::x86::ID_INS_PFRSQRT;
            break;

          case X86_INS_PFSUBR:
            tritonId = triton::arch::x86::ID_INS_PFSUBR;
            break;

          case X86_INS_PFSUB:
            tritonId = triton::arch::x86::ID_INS_PFSUB;
            break;

          case X86_INS_PHMINPOSUW:
            tritonId = triton::arch::x86::ID_INS_PHMINPOSUW;
            break;

          case X86_INS_PI2FD:
            tritonId = triton::arch::x86::ID_INS_PI2FD;
            break;

          case X86_INS_PI2FW:
            tritonId = triton::arch::x86::ID_INS_PI2FW;
            break;

          case X86_INS_PINSRB:
            tritonId = triton::arch::x86::ID_INS_PINSRB;
            break;

          case X86_INS_PINSRD:
            tritonId = triton::arch::x86::ID_INS_PINSRD;
            break;

          case X86_INS_PINSRQ:
            tritonId = triton::arch::x86::ID_INS_PINSRQ;
            break;

          case X86_INS_PMAXSB:
            tritonId = triton::arch::x86::ID_INS_PMAXSB;
            break;

          case X86_INS_PMAXSD:
            tritonId = triton::arch::x86::ID_INS_PMAXSD;
            break;

          case X86_INS_PMAXUD:
            tritonId = triton::arch::x86::ID_INS_PMAXUD;
            break;

          case X86_INS_PMAXUW:
            tritonId = triton::arch::x86::ID_INS_PMAXUW;
            break;

          case X86_INS_PMINSB:
            tritonId = triton::arch::x86::ID_INS_PMINSB;
            break;

          case X86_INS_PMINSD:
            tritonId = triton::arch::x86::ID_INS_PMINSD;
            break;

          case X86_INS_PMINUD:
            tritonId = triton::arch::x86::ID_INS_PMINUD;
            break;

          case X86_INS_PMINUW:
            tritonId = triton::arch::x86::ID_INS_PMINUW;
            break;

          case X86_INS_PMOVSXBD:
            tritonId = triton::arch::x86::ID_INS_PMOVSXBD;
            break;

          case X86_INS_PMOVSXBQ:
            tritonId = triton::arch::x86::ID_INS_PMOVSXBQ;
            break;

          case X86_INS_PMOVSXBW:
            tritonId = triton::arch::x86::ID_INS_PMOVSXBW;
            break;

          case X86_INS_PMOVSXDQ:
            tritonId = triton::arch::x86::ID_INS_PMOVSXDQ;
            break;

          case X86_INS_PMOVSXWD:
            tritonId = triton::arch::x86::ID_INS_PMOVSXWD;
            break;

          case X86_INS_PMOVSXWQ:
            tritonId = triton::arch::x86::ID_INS_PMOVSXWQ;
            break;

          case X86_INS_PMOVZXBD:
            tritonId = triton::arch::x86::ID_INS_PMOVZXBD;
            break;

          case X86_INS_PMOVZXBQ:
            tritonId = triton::arch::x86::ID_INS_PMOVZXBQ;
            break;

          case X86_INS_PMOVZXBW:
            tritonId = triton::arch::x86::ID_INS_PMOVZXBW;
            break;

          case X86_INS_PMOVZXDQ:
            tritonId = triton::arch::x86::ID_INS_PMOVZXDQ;
            break;

          case X86_INS_PMOVZXWD:
            tritonId = triton::arch::x86::ID_INS_PMOVZXWD;
            break;

          case X86_INS_PMOVZXWQ:
            tritonId = triton::arch::x86::ID_INS_PMOVZXWQ;
            break;

          case X86_INS_PMULDQ:
            tritonId = triton::arch::x86::ID_INS_PMULDQ;
            break;

          case X86_INS_PMULHRW:
            tritonId = triton::arch::x86::ID_INS_PMULHRW;
            break;

          case X86_INS_PMULLD:
            tritonId = triton::arch::x86::ID_INS_PMULLD;
            break;

          case X86_INS_POP:
            tritonId = triton::arch::x86::ID_INS_POP;
            break;

          case X86_INS_POPAW:
            tritonId = triton::arch::x86::ID_INS_POPAW;
            break;

          case X86_INS_POPAL:
            tritonId = triton::arch::x86::ID_INS_POPAL;
            break;

          case X86_INS_POPCNT:
            tritonId = triton::arch::x86::ID_INS_POPCNT;
            break;

          case X86_INS_POPF:
            tritonId = triton::arch::x86::ID_INS_POPF;
            break;

          case X86_INS_POPFD:
            tritonId = triton::arch::x86::ID_INS_POPFD;
            break;

          case X86_INS_POPFQ:
            tritonId = triton::arch::x86::ID_INS_POPFQ;
            break;

          case X86_INS_PREFETCH:
            tritonId = triton::arch::x86::ID_INS_PREFETCH;
            break;

          case X86_INS_PREFETCHNTA:
            tritonId = triton::arch::x86::ID_INS_PREFETCHNTA;
            break;

          case X86_INS_PREFETCHT0:
            tritonId = triton::arch::x86::ID_INS_PREFETCHT0;
            break;

          case X86_INS_PREFETCHT1:
            tritonId = triton::arch::x86::ID_INS_PREFETCHT1;
            break;

          case X86_INS_PREFETCHT2:
            tritonId = triton::arch::x86::ID_INS_PREFETCHT2;
            break;

          case X86_INS_PREFETCHW:
            tritonId = triton::arch::x86::ID_INS_PREFETCHW;
            break;

          case X86_INS_PSHUFD:
            tritonId = triton::arch::x86::ID_INS_PSHUFD;
            break;

          case X86_INS_PSHUFHW:
            tritonId = triton::arch::x86::ID_INS_PSHUFHW;
            break;

          case X86_INS_PSHUFLW:
            tritonId = triton::arch::x86::ID_INS_PSHUFLW;
            break;

          case X86_INS_PSLLDQ:
            tritonId = triton::arch::x86::ID_INS_PSLLDQ;
            break;

          case X86_INS_PSRLDQ:
            tritonId = triton::arch::x86::ID_INS_PSRLDQ;
            break;

          case X86_INS_PSWAPD:
            tritonId = triton::arch::x86::ID_INS_PSWAPD;
            break;

          case X86_INS_PTEST:
            tritonId = triton::arch::x86::ID_INS_PTEST;
            break;

          case X86_INS_PUNPCKHQDQ:
            tritonId = triton::arch::x86::ID_INS_PUNPCKHQDQ;
            break;

          case X86_INS_PUNPCKLQDQ:
            tritonId = triton::arch::x86::ID_INS_PUNPCKLQDQ;
            break;

          case X86_INS_PUSH:
            tritonId = triton::arch::x86::ID_INS_PUSH;
            break;

          case X86_INS_PUSHAW:
            tritonId = triton::arch::x86::ID_INS_PUSHAW;
            break;

          case X86_INS_PUSHAL:
            tritonId = triton::arch::x86::ID_INS_PUSHAL;
            break;

          case X86_INS_PUSHF:
            tritonId = triton::arch::x86::ID_INS_PUSHF;
            break;

          case X86_INS_PUSHFD:
            tritonId = triton::arch::x86::ID_INS_PUSHFD;
            break;

          case X86_INS_PUSHFQ:
            tritonId = triton::arch::x86::ID_INS_PUSHFQ;
            break;

          case X86_INS_RCL:
            tritonId = triton::arch::x86::ID_INS_RCL;
            break;

          case X86_INS_RCPPS:
            tritonId = triton::arch::x86::ID_INS_RCPPS;
            break;

          case X86_INS_RCPSS:
            tritonId = triton::arch::x86::ID_INS_RCPSS;
            break;

          case X86_INS_RCR:
            tritonId = triton::arch::x86::ID_INS_RCR;
            break;

          case X86_INS_RDFSBASE:
            tritonId = triton::arch::x86::ID_INS_RDFSBASE;
            break;

          case X86_INS_RDGSBASE:
            tritonId = triton::arch::x86::ID_INS_RDGSBASE;
            break;

          case X86_INS_RDMSR:
            tritonId = triton::arch::x86::ID_INS_RDMSR;
            break;

          case X86_INS_RDPMC:
            tritonId = triton::arch::x86::ID_INS_RDPMC;
            break;

          case X86_INS_RDRAND:
            tritonId = triton::arch::x86::ID_INS_RDRAND;
            break;

          case X86_INS_RDSEED:
            tritonId = triton::arch::x86::ID_INS_RDSEED;
            break;

          case X86_INS_RDTSC:
            tritonId = triton::arch::x86::ID_INS_RDTSC;
            break;

          case X86_INS_RDTSCP:
            tritonId = triton::arch::x86::ID_INS_RDTSCP;
            break;

          case X86_INS_ROL:
            tritonId = triton::arch::x86::ID_INS_ROL;
            break;

          case X86_INS_ROR:
            tritonId = triton::arch::x86::ID_INS_ROR;
            break;

          case X86_INS_RORX:
            tritonId = triton::arch::x86::ID_INS_RORX;
            break;

          case X86_INS_ROUNDPD:
            tritonId = triton::arch::x86::ID_INS_ROUNDPD;
            break;

          case X86_INS_ROUNDPS:
            tritonId = triton::arch::x86::ID_INS_ROUNDPS;
            break;

          case X86_INS_ROUNDSD:
            tritonId = triton::arch::x86::ID_INS_ROUNDSD;
            break;

          case X86_INS_ROUNDSS:
            tritonId = triton::arch::x86::ID_INS_ROUNDSS;
            break;

          case X86_INS_RSM:
            tritonId = triton::arch::x86::ID_INS_RSM;
            break;

          case X86_INS_RSQRTPS:
            tritonId = triton::arch::x86::ID_INS_RSQRTPS;
            break;

          case X86_INS_RSQRTSS:
            tritonId = triton::arch::x86::ID_INS_RSQRTSS;
            break;

          case X86_INS_SAHF:
            tritonId = triton::arch::x86::ID_INS_SAHF;
            break;

          case X86_INS_SAL:
            tritonId = triton::arch::x86::ID_INS_SAL;
            break;

          case X86_INS_SALC:
            tritonId = triton::arch::x86::ID_INS_SALC;
            break;

          case X86_INS_SAR:
            tritonId = triton::arch::x86::ID_INS_SAR;
            break;

          case X86_INS_SARX:
            tritonId = triton::arch::x86::ID_INS_SARX;
            break;

          case X86_INS_SBB:
            tritonId = triton::arch::x86::ID_INS_SBB;
            break;

          case X86_INS_SCASB:
            tritonId = triton::arch::x86::ID_INS_SCASB;
            break;

          case X86_INS_SCASD:
            tritonId = triton::arch::x86::ID_INS_SCASD;
            break;

          case X86_INS_SCASQ:
            tritonId = triton::arch::x86::ID_INS_SCASQ;
            break;

          case X86_INS_SCASW:
            tritonId = triton::arch::x86::ID_INS_SCASW;
            break;

          case X86_INS_SETAE:
            tritonId = triton::arch::x86::ID_INS_SETAE;
            break;

          case X86_INS_SETA:
            tritonId = triton::arch::x86::ID_INS_SETA;
            break;

          case X86_INS_SETBE:
            tritonId = triton::arch::x86::ID_INS_SETBE;
            break;

          case X86_INS_SETB:
            tritonId = triton::arch::x86::ID_INS_SETB;
            break;

          case X86_INS_SETE:
            tritonId = triton::arch::x86::ID_INS_SETE;
            break;

          case X86_INS_SETGE:
            tritonId = triton::arch::x86::ID_INS_SETGE;
            break;

          case X86_INS_SETG:
            tritonId = triton::arch::x86::ID_INS_SETG;
            break;

          case X86_INS_SETLE:
            tritonId = triton::arch::x86::ID_INS_SETLE;
            break;

          case X86_INS_SETL:
            tritonId = triton::arch::x86::ID_INS_SETL;
            break;

          case X86_INS_SETNE:
            tritonId = triton::arch::x86::ID_INS_SETNE;
            break;

          case X86_INS_SETNO:
            tritonId = triton::arch::x86::ID_INS_SETNO;
            break;

          case X86_INS_SETNP:
            tritonId = triton::arch::x86::ID_INS_SETNP;
            break;

          case X86_INS_SETNS:
            tritonId = triton::arch::x86::ID_INS_SETNS;
            break;

          case X86_INS_SETO:
            tritonId = triton::arch::x86::ID_INS_SETO;
            break;

          case X86_INS_SETP:
            tritonId = triton::arch::x86::ID_INS_SETP;
            break;

          case X86_INS_SETS:
            tritonId = triton::arch::x86::ID_INS_SETS;
            break;

          case X86_INS_SFENCE:
            tritonId = triton::arch::x86::ID_INS_SFENCE;
            break;

          case X86_INS_SGDT:
            tritonId = triton::arch::x86::ID_INS_SGDT;
            break;

          case X86_INS_SHA1MSG1:
            tritonId = triton::arch::x86::ID_INS_SHA1MSG1;
            break;

          case X86_INS_SHA1MSG2:
            tritonId = triton::arch::x86::ID_INS_SHA1MSG2;
            break;

          case X86_INS_SHA1NEXTE:
            tritonId = triton::arch::x86::ID_INS_SHA1NEXTE;
            break;

          case X86_INS_SHA1RNDS4:
            tritonId = triton::arch::x86::ID_INS_SHA1RNDS4;
            break;

          case X86_INS_SHA256MSG1:
            tritonId = triton::arch::x86::ID_INS_SHA256MSG1;
            break;

          case X86_INS_SHA256MSG2:
            tritonId = triton::arch::x86::ID_INS_SHA256MSG2;
            break;

          case X86_INS_SHA256RNDS2:
            tritonId = triton::arch::x86::ID_INS_SHA256RNDS2;
            break;

          case X86_INS_SHL:
            tritonId = triton::arch::x86::ID_INS_SHL;
            break;

          case X86_INS_SHLD:
            tritonId = triton::arch::x86::ID_INS_SHLD;
            break;

          case X86_INS_SHLX:
            tritonId = triton::arch::x86::ID_INS_SHLX;
            break;

          case X86_INS_SHR:
            tritonId = triton::arch::x86::ID_INS_SHR;
            break;

          case X86_INS_SHRD:
            tritonId = triton::arch::x86::ID_INS_SHRD;
            break;

          case X86_INS_SHRX:
            tritonId = triton::arch::x86::ID_INS_SHRX;
            break;

          case X86_INS_SHUFPD:
            tritonId = triton::arch::x86::ID_INS_SHUFPD;
            break;

          case X86_INS_SHUFPS:
            tritonId = triton::arch::x86::ID_INS_SHUFPS;
            break;

          case X86_INS_SIDT:
            tritonId = triton::arch::x86::ID_INS_SIDT;
            break;

          case X86_INS_FSIN:
            tritonId = triton::arch::x86::ID_INS_FSIN;
            break;

          case X86_INS_SKINIT:
            tritonId = triton::arch::x86::ID_INS_SKINIT;
            break;

          case X86_INS_SLDT:
            tritonId = triton::arch::x86::ID_INS_SLDT;
            break;

          case X86_INS_SMSW:
            tritonId = triton::arch::x86::ID_INS_SMSW;
            break;

          case X86_INS_SQRTPD:
            tritonId = triton::arch::x86::ID_INS_SQRTPD;
            break;

          case X86_INS_SQRTPS:
            tritonId = triton::arch::x86::ID_INS_SQRTPS;
            break;

          case X86_INS_SQRTSD:
            tritonId = triton::arch::x86::ID_INS_SQRTSD;
            break;

          case X86_INS_SQRTSS:
            tritonId = triton::arch::x86::ID_INS_SQRTSS;
            break;

          case X86_INS_FSQRT:
            tritonId = triton::arch::x86::ID_INS_FSQRT;
            break;

          case X86_INS_STAC:
            tritonId = triton::arch::x86::ID_INS_STAC;
            break;

          case X86_INS_STC:
            tritonId = triton::arch::x86::ID_INS_STC;
            break;

          case X86_INS_STD:
            tritonId = triton::arch::x86::ID_INS_STD;
            break;

          case X86_INS_STGI:
            tritonId = triton::arch::x86::ID_INS_STGI;
            break;

          case X86_INS_STI:
            tritonId = triton::arch::x86::ID_INS_STI;
            break;

          case X86_INS_STMXCSR:
            tritonId = triton::arch::x86::ID_INS_STMXCSR;
            break;

          case X86_INS_STOSB:
            tritonId = triton::arch::x86::ID_INS_STOSB;
            break;

          case X86_INS_STOSD:
            tritonId = triton::arch::x86::ID_INS_STOSD;
            break;

          case X86_INS_STOSQ:
            tritonId = triton::arch::x86::ID_INS_STOSQ;
            break;

          case X86_INS_STOSW:
            tritonId = triton::arch::x86::ID_INS_STOSW;
            break;

          case X86_INS_STR:
            tritonId = triton::arch::x86::ID_INS_STR;
            break;

          case X86_INS_FST:
            tritonId = triton::arch::x86::ID_INS_FST;
            break;

          case X86_INS_FSTP:
            tritonId = triton::arch::x86::ID_INS_FSTP;
            break;

          case X86_INS_FSTPNCE:
            tritonId = triton::arch::x86::ID_INS_FSTPNCE;
            break;

          case X86_INS_SUBPD:
            tritonId = triton::arch::x86::ID_INS_SUBPD;
            break;

          case X86_INS_SUBPS:
            tritonId = triton::arch::x86::ID_INS_SUBPS;
            break;

          case X86_INS_FSUBR:
            tritonId = triton::arch::x86::ID_INS_FSUBR;
            break;

          case X86_INS_FISUBR:
            tritonId = triton::arch::x86::ID_INS_FISUBR;
            break;

          case X86_INS_FSUBRP:
            tritonId = triton::arch::x86::ID_INS_FSUBRP;
            break;

          case X86_INS_SUBSD:
            tritonId = triton::arch::x86::ID_INS_SUBSD;
            break;

          case X86_INS_SUBSS:
            tritonId = triton::arch::x86::ID_INS_SUBSS;
            break;

          case X86_INS_FSUB:
            tritonId = triton::arch::x86::ID_INS_FSUB;
            break;

          case X86_INS_FISUB:
            tritonId = triton::arch::x86::ID_INS_FISUB;
            break;

          case X86_INS_FSUBP:
            tritonId = triton::arch::x86::ID_INS_FSUBP;
            break;

          case X86_INS_SWAPGS:
            tritonId = triton::arch::x86::ID_INS_SWAPGS;
            break;

          case X86_INS_SYSCALL:
            tritonId = triton::arch::x86::ID_INS_SYSCALL;
            break;

          case X86_INS_SYSENTER:
            tritonId = triton::arch::x86::ID_INS_SYSENTER;
            break;

          case X86_INS_SYSEXIT:
            tritonId = triton::arch::x86::ID_INS_SYSEXIT;
            break;

          case X86_INS_SYSRET:
            tritonId = triton::arch::x86::ID_INS_SYSRET;
            break;

          case X86_INS_T1MSKC:
            tritonId = triton::arch::x86::ID_INS_T1MSKC;
            break;

          case X86_INS_TEST:
            tritonId = triton::arch::x86::ID_INS_TEST;
            break;

          case X86_INS_UD2:
            tritonId = triton::arch::x86::ID_INS_UD2;
            break;

          case X86_INS_FTST:
            tritonId = triton::arch::x86::ID_INS_FTST;
            break;

          case X86_INS_TZCNT:
            tritonId = triton::arch::x86::ID_INS_TZCNT;
            break;

          case X86_INS_TZMSK:
            tritonId = triton::arch::x86::ID_INS_TZMSK;
            break;

          case X86_INS_FUCOMPI:
            tritonId = triton::arch::x86::ID_INS_FUCOMPI;
            break;

          case X86_INS_FUCOMI:
            tritonId = triton::arch::x86::ID_INS_FUCOMI;
            break;

          case X86_INS_FUCOMPP:
            tritonId = triton::arch::x86::ID_INS_FUCOMPP;
            break;

          case X86_INS_FUCOMP:
            tritonId = triton::arch::x86::ID_INS_FUCOMP;
            break;

          case X86_INS_FUCOM:
            tritonId = triton::arch::x86::ID_INS_FUCOM;
            break;

          case X86_INS_UD2B:
            tritonId = triton::arch::x86::ID_INS_UD2B;
            break;

          case X86_INS_UNPCKHPD:
            tritonId = triton::arch::x86::ID_INS_UNPCKHPD;
            break;

          case X86_INS_UNPCKHPS:
            tritonId = triton::arch::x86::ID_INS_UNPCKHPS;
            break;

          case X86_INS_UNPCKLPD:
            tritonId = triton::arch::x86::ID_INS_UNPCKLPD;
            break;

          case X86_INS_UNPCKLPS:
            tritonId = triton::arch::x86::ID_INS_UNPCKLPS;
            break;

          case X86_INS_VADDPD:
            tritonId = triton::arch::x86::ID_INS_VADDPD;
            break;

          case X86_INS_VADDPS:
            tritonId = triton::arch::x86::ID_INS_VADDPS;
            break;

          case X86_INS_VADDSD:
            tritonId = triton::arch::x86::ID_INS_VADDSD;
            break;

          case X86_INS_VADDSS:
            tritonId = triton::arch::x86::ID_INS_VADDSS;
            break;

          case X86_INS_VADDSUBPD:
            tritonId = triton::arch::x86::ID_INS_VADDSUBPD;
            break;

          case X86_INS_VADDSUBPS:
            tritonId = triton::arch::x86::ID_INS_VADDSUBPS;
            break;

          case X86_INS_VAESDECLAST:
            tritonId = triton::arch::x86::ID_INS_VAESDECLAST;
            break;

          case X86_INS_VAESDEC:
            tritonId = triton::arch::x86::ID_INS_VAESDEC;
            break;

          case X86_INS_VAESENCLAST:
            tritonId = triton::arch::x86::ID_INS_VAESENCLAST;
            break;

          case X86_INS_VAESENC:
            tritonId = triton::arch::x86::ID_INS_VAESENC;
            break;

          case X86_INS_VAESIMC:
            tritonId = triton::arch::x86::ID_INS_VAESIMC;
            break;

          case X86_INS_VAESKEYGENASSIST:
            tritonId = triton::arch::x86::ID_INS_VAESKEYGENASSIST;
            break;

          case X86_INS_VALIGND:
            tritonId = triton::arch::x86::ID_INS_VALIGND;
            break;

          case X86_INS_VALIGNQ:
            tritonId = triton::arch::x86::ID_INS_VALIGNQ;
            break;

          case X86_INS_VANDNPD:
            tritonId = triton::arch::x86::ID_INS_VANDNPD;
            break;

          case X86_INS_VANDNPS:
            tritonId = triton::arch::x86::ID_INS_VANDNPS;
            break;

          case X86_INS_VANDPD:
            tritonId = triton::arch::x86::ID_INS_VANDPD;
            break;

          case X86_INS_VANDPS:
            tritonId = triton::arch::x86::ID_INS_VANDPS;
            break;

          case X86_INS_VBLENDMPD:
            tritonId = triton::arch::x86::ID_INS_VBLENDMPD;
            break;

          case X86_INS_VBLENDMPS:
            tritonId = triton::arch::x86::ID_INS_VBLENDMPS;
            break;

          case X86_INS_VBLENDPD:
            tritonId = triton::arch::x86::ID_INS_VBLENDPD;
            break;

          case X86_INS_VBLENDPS:
            tritonId = triton::arch::x86::ID_INS_VBLENDPS;
            break;

          case X86_INS_VBLENDVPD:
            tritonId = triton::arch::x86::ID_INS_VBLENDVPD;
            break;

          case X86_INS_VBLENDVPS:
            tritonId = triton::arch::x86::ID_INS_VBLENDVPS;
            break;

          case X86_INS_VBROADCASTF128:
            tritonId = triton::arch::x86::ID_INS_VBROADCASTF128;
            break;

          case X86_INS_VBROADCASTI128:
            tritonId = triton::arch::x86::ID_INS_VBROADCASTI128;
            break;

          case X86_INS_VBROADCASTI32X4:
            tritonId = triton::arch::x86::ID_INS_VBROADCASTI32X4;
            break;

          case X86_INS_VBROADCASTI64X4:
            tritonId = triton::arch::x86::ID_INS_VBROADCASTI64X4;
            break;

          case X86_INS_VBROADCASTSD:
            tritonId = triton::arch::x86::ID_INS_VBROADCASTSD;
            break;

          case X86_INS_VBROADCASTSS:
            tritonId = triton::arch::x86::ID_INS_VBROADCASTSS;
            break;

          case X86_INS_VCMPPD:
            tritonId = triton::arch::x86::ID_INS_VCMPPD;
            break;

          case X86_INS_VCMPPS:
            tritonId = triton::arch::x86::ID_INS_VCMPPS;
            break;

          case X86_INS_VCMPSD:
            tritonId = triton::arch::x86::ID_INS_VCMPSD;
            break;

          case X86_INS_VCMPSS:
            tritonId = triton::arch::x86::ID_INS_VCMPSS;
            break;

          case X86_INS_VCVTDQ2PD:
            tritonId = triton::arch::x86::ID_INS_VCVTDQ2PD;
            break;

          case X86_INS_VCVTDQ2PS:
            tritonId = triton::arch::x86::ID_INS_VCVTDQ2PS;
            break;

          case X86_INS_VCVTPD2DQX:
            tritonId = triton::arch::x86::ID_INS_VCVTPD2DQX;
            break;

          case X86_INS_VCVTPD2DQ:
            tritonId = triton::arch::x86::ID_INS_VCVTPD2DQ;
            break;

          case X86_INS_VCVTPD2PSX:
            tritonId = triton::arch::x86::ID_INS_VCVTPD2PSX;
            break;

          case X86_INS_VCVTPD2PS:
            tritonId = triton::arch::x86::ID_INS_VCVTPD2PS;
            break;

          case X86_INS_VCVTPD2UDQ:
            tritonId = triton::arch::x86::ID_INS_VCVTPD2UDQ;
            break;

          case X86_INS_VCVTPH2PS:
            tritonId = triton::arch::x86::ID_INS_VCVTPH2PS;
            break;

          case X86_INS_VCVTPS2DQ:
            tritonId = triton::arch::x86::ID_INS_VCVTPS2DQ;
            break;

          case X86_INS_VCVTPS2PD:
            tritonId = triton::arch::x86::ID_INS_VCVTPS2PD;
            break;

          case X86_INS_VCVTPS2PH:
            tritonId = triton::arch::x86::ID_INS_VCVTPS2PH;
            break;

          case X86_INS_VCVTPS2UDQ:
            tritonId = triton::arch::x86::ID_INS_VCVTPS2UDQ;
            break;

          case X86_INS_VCVTSD2SI:
            tritonId = triton::arch::x86::ID_INS_VCVTSD2SI;
            break;

          case X86_INS_VCVTSD2USI:
            tritonId = triton::arch::x86::ID_INS_VCVTSD2USI;
            break;

          case X86_INS_VCVTSS2SI:
            tritonId = triton::arch::x86::ID_INS_VCVTSS2SI;
            break;

          case X86_INS_VCVTSS2USI:
            tritonId = triton::arch::x86::ID_INS_VCVTSS2USI;
            break;

          case X86_INS_VCVTTPD2DQX:
            tritonId = triton::arch::x86::ID_INS_VCVTTPD2DQX;
            break;

          case X86_INS_VCVTTPD2DQ:
            tritonId = triton::arch::x86::ID_INS_VCVTTPD2DQ;
            break;

          case X86_INS_VCVTTPD2UDQ:
            tritonId = triton::arch::x86::ID_INS_VCVTTPD2UDQ;
            break;

          case X86_INS_VCVTTPS2DQ:
            tritonId = triton::arch::x86::ID_INS_VCVTTPS2DQ;
            break;

          case X86_INS_VCVTTPS2UDQ:
            tritonId = triton::arch::x86::ID_INS_VCVTTPS2UDQ;
            break;

          case X86_INS_VCVTUDQ2PD:
            tritonId = triton::arch::x86::ID_INS_VCVTUDQ2PD;
            break;

          case X86_INS_VCVTUDQ2PS:
            tritonId = triton::arch::x86::ID_INS_VCVTUDQ2PS;
            break;

          case X86_INS_VDIVPD:
            tritonId = triton::arch::x86::ID_INS_VDIVPD;
            break;

          case X86_INS_VDIVPS:
            tritonId = triton::arch::x86::ID_INS_VDIVPS;
            break;

          case X86_INS_VDIVSD:
            tritonId = triton::arch::x86::ID_INS_VDIVSD;
            break;

          case X86_INS_VDIVSS:
            tritonId = triton::arch::x86::ID_INS_VDIVSS;
            break;

          case X86_INS_VDPPD:
            tritonId = triton::arch::x86::ID_INS_VDPPD;
            break;

          case X86_INS_VDPPS:
            tritonId = triton::arch::x86::ID_INS_VDPPS;
            break;

          case X86_INS_VERR:
            tritonId = triton::arch::x86::ID_INS_VERR;
            break;

          case X86_INS_VERW:
            tritonId = triton::arch::x86::ID_INS_VERW;
            break;

          case X86_INS_VEXTRACTF128:
            tritonId = triton::arch::x86::ID_INS_VEXTRACTF128;
            break;

          case X86_INS_VEXTRACTF32X4:
            tritonId = triton::arch::x86::ID_INS_VEXTRACTF32X4;
            break;

          case X86_INS_VEXTRACTF64X4:
            tritonId = triton::arch::x86::ID_INS_VEXTRACTF64X4;
            break;

          case X86_INS_VEXTRACTI128:
            tritonId = triton::arch::x86::ID_INS_VEXTRACTI128;
            break;

          case X86_INS_VEXTRACTI32X4:
            tritonId = triton::arch::x86::ID_INS_VEXTRACTI32X4;
            break;

          case X86_INS_VEXTRACTI64X4:
            tritonId = triton::arch::x86::ID_INS_VEXTRACTI64X4;
            break;

          case X86_INS_VEXTRACTPS:
            tritonId = triton::arch::x86::ID_INS_VEXTRACTPS;
            break;

          case X86_INS_VFMADD132PD:
            tritonId = triton::arch::x86::ID_INS_VFMADD132PD;
            break;

          case X86_INS_VFMADD132PS:
            tritonId = triton::arch::x86::ID_INS_VFMADD132PS;
            break;

          case X86_INS_VFMADD213PD:
            tritonId = triton::arch::x86::ID_INS_VFMADD213PD;
            break;

          case X86_INS_VFMADD213PS:
            tritonId = triton::arch::x86::ID_INS_VFMADD213PS;
            break;

          case X86_INS_VFMADDPD:
            tritonId = triton::arch::x86::ID_INS_VFMADDPD;
            break;

          case X86_INS_VFMADD231PD:
            tritonId = triton::arch::x86::ID_INS_VFMADD231PD;
            break;

          case X86_INS_VFMADDPS:
            tritonId = triton::arch::x86::ID_INS_VFMADDPS;
            break;

          case X86_INS_VFMADD231PS:
            tritonId = triton::arch::x86::ID_INS_VFMADD231PS;
            break;

          case X86_INS_VFMADDSD:
            tritonId = triton::arch::x86::ID_INS_VFMADDSD;
            break;

          case X86_INS_VFMADD213SD:
            tritonId = triton::arch::x86::ID_INS_VFMADD213SD;
            break;

          case X86_INS_VFMADD132SD:
            tritonId = triton::arch::x86::ID_INS_VFMADD132SD;
            break;

          case X86_INS_VFMADD231SD:
            tritonId = triton::arch::x86::ID_INS_VFMADD231SD;
            break;

          case X86_INS_VFMADDSS:
            tritonId = triton::arch::x86::ID_INS_VFMADDSS;
            break;

          case X86_INS_VFMADD213SS:
            tritonId = triton::arch::x86::ID_INS_VFMADD213SS;
            break;

          case X86_INS_VFMADD132SS:
            tritonId = triton::arch::x86::ID_INS_VFMADD132SS;
            break;

          case X86_INS_VFMADD231SS:
            tritonId = triton::arch::x86::ID_INS_VFMADD231SS;
            break;

          case X86_INS_VFMADDSUB132PD:
            tritonId = triton::arch::x86::ID_INS_VFMADDSUB132PD;
            break;

          case X86_INS_VFMADDSUB132PS:
            tritonId = triton::arch::x86::ID_INS_VFMADDSUB132PS;
            break;

          case X86_INS_VFMADDSUB213PD:
            tritonId = triton::arch::x86::ID_INS_VFMADDSUB213PD;
            break;

          case X86_INS_VFMADDSUB213PS:
            tritonId = triton::arch::x86::ID_INS_VFMADDSUB213PS;
            break;

          case X86_INS_VFMADDSUBPD:
            tritonId = triton::arch::x86::ID_INS_VFMADDSUBPD;
            break;

          case X86_INS_VFMADDSUB231PD:
            tritonId = triton::arch::x86::ID_INS_VFMADDSUB231PD;
            break;

          case X86_INS_VFMADDSUBPS:
            tritonId = triton::arch::x86::ID_INS_VFMADDSUBPS;
            break;

          case X86_INS_VFMADDSUB231PS:
            tritonId = triton::arch::x86::ID_INS_VFMADDSUB231PS;
            break;

          case X86_INS_VFMSUB132PD:
            tritonId = triton::arch::x86::ID_INS_VFMSUB132PD;
            break;

          case X86_INS_VFMSUB132PS:
            tritonId = triton::arch::x86::ID_INS_VFMSUB132PS;
            break;

          case X86_INS_VFMSUB213PD:
            tritonId = triton::arch::x86::ID_INS_VFMSUB213PD;
            break;

          case X86_INS_VFMSUB213PS:
            tritonId = triton::arch::x86::ID_INS_VFMSUB213PS;
            break;

          case X86_INS_VFMSUBADD132PD:
            tritonId = triton::arch::x86::ID_INS_VFMSUBADD132PD;
            break;

          case X86_INS_VFMSUBADD132PS:
            tritonId = triton::arch::x86::ID_INS_VFMSUBADD132PS;
            break;

          case X86_INS_VFMSUBADD213PD:
            tritonId = triton::arch::x86::ID_INS_VFMSUBADD213PD;
            break;

          case X86_INS_VFMSUBADD213PS:
            tritonId = triton::arch::x86::ID_INS_VFMSUBADD213PS;
            break;

          case X86_INS_VFMSUBADDPD:
            tritonId = triton::arch::x86::ID_INS_VFMSUBADDPD;
            break;

          case X86_INS_VFMSUBADD231PD:
            tritonId = triton::arch::x86::ID_INS_VFMSUBADD231PD;
            break;

          case X86_INS_VFMSUBADDPS:
            tritonId = triton::arch::x86::ID_INS_VFMSUBADDPS;
            break;

          case X86_INS_VFMSUBADD231PS:
            tritonId = triton::arch::x86::ID_INS_VFMSUBADD231PS;
            break;

          case X86_INS_VFMSUBPD:
            tritonId = triton::arch::x86::ID_INS_VFMSUBPD;
            break;

          case X86_INS_VFMSUB231PD:
            tritonId = triton::arch::x86::ID_INS_VFMSUB231PD;
            break;

          case X86_INS_VFMSUBPS:
            tritonId = triton::arch::x86::ID_INS_VFMSUBPS;
            break;

          case X86_INS_VFMSUB231PS:
            tritonId = triton::arch::x86::ID_INS_VFMSUB231PS;
            break;

          case X86_INS_VFMSUBSD:
            tritonId = triton::arch::x86::ID_INS_VFMSUBSD;
            break;

          case X86_INS_VFMSUB213SD:
            tritonId = triton::arch::x86::ID_INS_VFMSUB213SD;
            break;

          case X86_INS_VFMSUB132SD:
            tritonId = triton::arch::x86::ID_INS_VFMSUB132SD;
            break;

          case X86_INS_VFMSUB231SD:
            tritonId = triton::arch::x86::ID_INS_VFMSUB231SD;
            break;

          case X86_INS_VFMSUBSS:
            tritonId = triton::arch::x86::ID_INS_VFMSUBSS;
            break;

          case X86_INS_VFMSUB213SS:
            tritonId = triton::arch::x86::ID_INS_VFMSUB213SS;
            break;

          case X86_INS_VFMSUB132SS:
            tritonId = triton::arch::x86::ID_INS_VFMSUB132SS;
            break;

          case X86_INS_VFMSUB231SS:
            tritonId = triton::arch::x86::ID_INS_VFMSUB231SS;
            break;

          case X86_INS_VFNMADD132PD:
            tritonId = triton::arch::x86::ID_INS_VFNMADD132PD;
            break;

          case X86_INS_VFNMADD132PS:
            tritonId = triton::arch::x86::ID_INS_VFNMADD132PS;
            break;

          case X86_INS_VFNMADD213PD:
            tritonId = triton::arch::x86::ID_INS_VFNMADD213PD;
            break;

          case X86_INS_VFNMADD213PS:
            tritonId = triton::arch::x86::ID_INS_VFNMADD213PS;
            break;

          case X86_INS_VFNMADDPD:
            tritonId = triton::arch::x86::ID_INS_VFNMADDPD;
            break;

          case X86_INS_VFNMADD231PD:
            tritonId = triton::arch::x86::ID_INS_VFNMADD231PD;
            break;

          case X86_INS_VFNMADDPS:
            tritonId = triton::arch::x86::ID_INS_VFNMADDPS;
            break;

          case X86_INS_VFNMADD231PS:
            tritonId = triton::arch::x86::ID_INS_VFNMADD231PS;
            break;

          case X86_INS_VFNMADDSD:
            tritonId = triton::arch::x86::ID_INS_VFNMADDSD;
            break;

          case X86_INS_VFNMADD213SD:
            tritonId = triton::arch::x86::ID_INS_VFNMADD213SD;
            break;

          case X86_INS_VFNMADD132SD:
            tritonId = triton::arch::x86::ID_INS_VFNMADD132SD;
            break;

          case X86_INS_VFNMADD231SD:
            tritonId = triton::arch::x86::ID_INS_VFNMADD231SD;
            break;

          case X86_INS_VFNMADDSS:
            tritonId = triton::arch::x86::ID_INS_VFNMADDSS;
            break;

          case X86_INS_VFNMADD213SS:
            tritonId = triton::arch::x86::ID_INS_VFNMADD213SS;
            break;

          case X86_INS_VFNMADD132SS:
            tritonId = triton::arch::x86::ID_INS_VFNMADD132SS;
            break;

          case X86_INS_VFNMADD231SS:
            tritonId = triton::arch::x86::ID_INS_VFNMADD231SS;
            break;

          case X86_INS_VFNMSUB132PD:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB132PD;
            break;

          case X86_INS_VFNMSUB132PS:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB132PS;
            break;

          case X86_INS_VFNMSUB213PD:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB213PD;
            break;

          case X86_INS_VFNMSUB213PS:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB213PS;
            break;

          case X86_INS_VFNMSUBPD:
            tritonId = triton::arch::x86::ID_INS_VFNMSUBPD;
            break;

          case X86_INS_VFNMSUB231PD:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB231PD;
            break;

          case X86_INS_VFNMSUBPS:
            tritonId = triton::arch::x86::ID_INS_VFNMSUBPS;
            break;

          case X86_INS_VFNMSUB231PS:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB231PS;
            break;

          case X86_INS_VFNMSUBSD:
            tritonId = triton::arch::x86::ID_INS_VFNMSUBSD;
            break;

          case X86_INS_VFNMSUB213SD:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB213SD;
            break;

          case X86_INS_VFNMSUB132SD:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB132SD;
            break;

          case X86_INS_VFNMSUB231SD:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB231SD;
            break;

          case X86_INS_VFNMSUBSS:
            tritonId = triton::arch::x86::ID_INS_VFNMSUBSS;
            break;

          case X86_INS_VFNMSUB213SS:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB213SS;
            break;

          case X86_INS_VFNMSUB132SS:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB132SS;
            break;

          case X86_INS_VFNMSUB231SS:
            tritonId = triton::arch::x86::ID_INS_VFNMSUB231SS;
            break;

          case X86_INS_VFRCZPD:
            tritonId = triton::arch::x86::ID_INS_VFRCZPD;
            break;

          case X86_INS_VFRCZPS:
            tritonId = triton::arch::x86::ID_INS_VFRCZPS;
            break;

          case X86_INS_VFRCZSD:
            tritonId = triton::arch::x86::ID_INS_VFRCZSD;
            break;

          case X86_INS_VFRCZSS:
            tritonId = triton::arch::x86::ID_INS_VFRCZSS;
            break;

          case X86_INS_VORPD:
            tritonId = triton::arch::x86::ID_INS_VORPD;
            break;

          case X86_INS_VORPS:
            tritonId = triton::arch::x86::ID_INS_VORPS;
            break;

          case X86_INS_VXORPD:
            tritonId = triton::arch::x86::ID_INS_VXORPD;
            break;

          case X86_INS_VXORPS:
            tritonId = triton::arch::x86::ID_INS_VXORPS;
            break;

          case X86_INS_VGATHERDPD:
            tritonId = triton::arch::x86::ID_INS_VGATHERDPD;
            break;

          case X86_INS_VGATHERDPS:
            tritonId = triton::arch::x86::ID_INS_VGATHERDPS;
            break;

          case X86_INS_VGATHERPF0DPD:
            tritonId = triton::arch::x86::ID_INS_VGATHERPF0DPD;
            break;

          case X86_INS_VGATHERPF0DPS:
            tritonId = triton::arch::x86::ID_INS_VGATHERPF0DPS;
            break;

          case X86_INS_VGATHERPF0QPD:
            tritonId = triton::arch::x86::ID_INS_VGATHERPF0QPD;
            break;

          case X86_INS_VGATHERPF0QPS:
            tritonId = triton::arch::x86::ID_INS_VGATHERPF0QPS;
            break;

          case X86_INS_VGATHERPF1DPD:
            tritonId = triton::arch::x86::ID_INS_VGATHERPF1DPD;
            break;

          case X86_INS_VGATHERPF1DPS:
            tritonId = triton::arch::x86::ID_INS_VGATHERPF1DPS;
            break;

          case X86_INS_VGATHERPF1QPD:
            tritonId = triton::arch::x86::ID_INS_VGATHERPF1QPD;
            break;

          case X86_INS_VGATHERPF1QPS:
            tritonId = triton::arch::x86::ID_INS_VGATHERPF1QPS;
            break;

          case X86_INS_VGATHERQPD:
            tritonId = triton::arch::x86::ID_INS_VGATHERQPD;
            break;

          case X86_INS_VGATHERQPS:
            tritonId = triton::arch::x86::ID_INS_VGATHERQPS;
            break;

          case X86_INS_VHADDPD:
            tritonId = triton::arch::x86::ID_INS_VHADDPD;
            break;

          case X86_INS_VHADDPS:
            tritonId = triton::arch::x86::ID_INS_VHADDPS;
            break;

          case X86_INS_VHSUBPD:
            tritonId = triton::arch::x86::ID_INS_VHSUBPD;
            break;

          case X86_INS_VHSUBPS:
            tritonId = triton::arch::x86::ID_INS_VHSUBPS;
            break;

          case X86_INS_VINSERTF128:
            tritonId = triton::arch::x86::ID_INS_VINSERTF128;
            break;

          case X86_INS_VINSERTF32X4:
            tritonId = triton::arch::x86::ID_INS_VINSERTF32X4;
            break;

          case X86_INS_VINSERTF64X4:
            tritonId = triton::arch::x86::ID_INS_VINSERTF64X4;
            break;

          case X86_INS_VINSERTI128:
            tritonId = triton::arch::x86::ID_INS_VINSERTI128;
            break;

          case X86_INS_VINSERTI32X4:
            tritonId = triton::arch::x86::ID_INS_VINSERTI32X4;
            break;

          case X86_INS_VINSERTI64X4:
            tritonId = triton::arch::x86::ID_INS_VINSERTI64X4;
            break;

          case X86_INS_VINSERTPS:
            tritonId = triton::arch::x86::ID_INS_VINSERTPS;
            break;

          case X86_INS_VLDDQU:
            tritonId = triton::arch::x86::ID_INS_VLDDQU;
            break;

          case X86_INS_VLDMXCSR:
            tritonId = triton::arch::x86::ID_INS_VLDMXCSR;
            break;

          case X86_INS_VMASKMOVDQU:
            tritonId = triton::arch::x86::ID_INS_VMASKMOVDQU;
            break;

          case X86_INS_VMASKMOVPD:
            tritonId = triton::arch::x86::ID_INS_VMASKMOVPD;
            break;

          case X86_INS_VMASKMOVPS:
            tritonId = triton::arch::x86::ID_INS_VMASKMOVPS;
            break;

          case X86_INS_VMAXPD:
            tritonId = triton::arch::x86::ID_INS_VMAXPD;
            break;

          case X86_INS_VMAXPS:
            tritonId = triton::arch::x86::ID_INS_VMAXPS;
            break;

          case X86_INS_VMAXSD:
            tritonId = triton::arch::x86::ID_INS_VMAXSD;
            break;

          case X86_INS_VMAXSS:
            tritonId = triton::arch::x86::ID_INS_VMAXSS;
            break;

          case X86_INS_VMCALL:
            tritonId = triton::arch::x86::ID_INS_VMCALL;
            break;

          case X86_INS_VMCLEAR:
            tritonId = triton::arch::x86::ID_INS_VMCLEAR;
            break;

          case X86_INS_VMFUNC:
            tritonId = triton::arch::x86::ID_INS_VMFUNC;
            break;

          case X86_INS_VMINPD:
            tritonId = triton::arch::x86::ID_INS_VMINPD;
            break;

          case X86_INS_VMINPS:
            tritonId = triton::arch::x86::ID_INS_VMINPS;
            break;

          case X86_INS_VMINSD:
            tritonId = triton::arch::x86::ID_INS_VMINSD;
            break;

          case X86_INS_VMINSS:
            tritonId = triton::arch::x86::ID_INS_VMINSS;
            break;

          case X86_INS_VMLAUNCH:
            tritonId = triton::arch::x86::ID_INS_VMLAUNCH;
            break;

          case X86_INS_VMLOAD:
            tritonId = triton::arch::x86::ID_INS_VMLOAD;
            break;

          case X86_INS_VMMCALL:
            tritonId = triton::arch::x86::ID_INS_VMMCALL;
            break;

          case X86_INS_VMOVQ:
            tritonId = triton::arch::x86::ID_INS_VMOVQ;
            break;

          case X86_INS_VMOVDDUP:
            tritonId = triton::arch::x86::ID_INS_VMOVDDUP;
            break;

          case X86_INS_VMOVD:
            tritonId = triton::arch::x86::ID_INS_VMOVD;
            break;

          case X86_INS_VMOVDQA32:
            tritonId = triton::arch::x86::ID_INS_VMOVDQA32;
            break;

          case X86_INS_VMOVDQA64:
            tritonId = triton::arch::x86::ID_INS_VMOVDQA64;
            break;

          case X86_INS_VMOVDQA:
            tritonId = triton::arch::x86::ID_INS_VMOVDQA;
            break;

          case X86_INS_VMOVDQU16:
            tritonId = triton::arch::x86::ID_INS_VMOVDQU16;
            break;

          case X86_INS_VMOVDQU32:
            tritonId = triton::arch::x86::ID_INS_VMOVDQU32;
            break;

          case X86_INS_VMOVDQU64:
            tritonId = triton::arch::x86::ID_INS_VMOVDQU64;
            break;

          case X86_INS_VMOVDQU8:
            tritonId = triton::arch::x86::ID_INS_VMOVDQU8;
            break;

          case X86_INS_VMOVDQU:
            tritonId = triton::arch::x86::ID_INS_VMOVDQU;
            break;

          case X86_INS_VMOVHLPS:
            tritonId = triton::arch::x86::ID_INS_VMOVHLPS;
            break;

          case X86_INS_VMOVHPD:
            tritonId = triton::arch::x86::ID_INS_VMOVHPD;
            break;

          case X86_INS_VMOVHPS:
            tritonId = triton::arch::x86::ID_INS_VMOVHPS;
            break;

          case X86_INS_VMOVLHPS:
            tritonId = triton::arch::x86::ID_INS_VMOVLHPS;
            break;

          case X86_INS_VMOVLPD:
            tritonId = triton::arch::x86::ID_INS_VMOVLPD;
            break;

          case X86_INS_VMOVLPS:
            tritonId = triton::arch::x86::ID_INS_VMOVLPS;
            break;

          case X86_INS_VMOVMSKPD:
            tritonId = triton::arch::x86::ID_INS_VMOVMSKPD;
            break;

          case X86_INS_VMOVMSKPS:
            tritonId = triton::arch::x86::ID_INS_VMOVMSKPS;
            break;

          case X86_INS_VMOVNTDQA:
            tritonId = triton::arch::x86::ID_INS_VMOVNTDQA;
            break;

          case X86_INS_VMOVNTDQ:
            tritonId = triton::arch::x86::ID_INS_VMOVNTDQ;
            break;

          case X86_INS_VMOVNTPD:
            tritonId = triton::arch::x86::ID_INS_VMOVNTPD;
            break;

          case X86_INS_VMOVNTPS:
            tritonId = triton::arch::x86::ID_INS_VMOVNTPS;
            break;

          case X86_INS_VMOVSD:
            tritonId = triton::arch::x86::ID_INS_VMOVSD;
            break;

          case X86_INS_VMOVSHDUP:
            tritonId = triton::arch::x86::ID_INS_VMOVSHDUP;
            break;

          case X86_INS_VMOVSLDUP:
            tritonId = triton::arch::x86::ID_INS_VMOVSLDUP;
            break;

          case X86_INS_VMOVSS:
            tritonId = triton::arch::x86::ID_INS_VMOVSS;
            break;

          case X86_INS_VMOVUPD:
            tritonId = triton::arch::x86::ID_INS_VMOVUPD;
            break;

          case X86_INS_VMOVUPS:
            tritonId = triton::arch::x86::ID_INS_VMOVUPS;
            break;

          case X86_INS_VMPSADBW:
            tritonId = triton::arch::x86::ID_INS_VMPSADBW;
            break;

          case X86_INS_VMPTRLD:
            tritonId = triton::arch::x86::ID_INS_VMPTRLD;
            break;

          case X86_INS_VMPTRST:
            tritonId = triton::arch::x86::ID_INS_VMPTRST;
            break;

          case X86_INS_VMREAD:
            tritonId = triton::arch::x86::ID_INS_VMREAD;
            break;

          case X86_INS_VMRESUME:
            tritonId = triton::arch::x86::ID_INS_VMRESUME;
            break;

          case X86_INS_VMRUN:
            tritonId = triton::arch::x86::ID_INS_VMRUN;
            break;

          case X86_INS_VMSAVE:
            tritonId = triton::arch::x86::ID_INS_VMSAVE;
            break;

          case X86_INS_VMULPD:
            tritonId = triton::arch::x86::ID_INS_VMULPD;
            break;

          case X86_INS_VMULPS:
            tritonId = triton::arch::x86::ID_INS_VMULPS;
            break;

          case X86_INS_VMULSD:
            tritonId = triton::arch::x86::ID_INS_VMULSD;
            break;

          case X86_INS_VMULSS:
            tritonId = triton::arch::x86::ID_INS_VMULSS;
            break;

          case X86_INS_VMWRITE:
            tritonId = triton::arch::x86::ID_INS_VMWRITE;
            break;

          case X86_INS_VMXOFF:
            tritonId = triton::arch::x86::ID_INS_VMXOFF;
            break;

          case X86_INS_VMXON:
            tritonId = triton::arch::x86::ID_INS_VMXON;
            break;

          case X86_INS_VPABSB:
            tritonId = triton::arch::x86::ID_INS_VPABSB;
            break;

          case X86_INS_VPABSD:
            tritonId = triton::arch::x86::ID_INS_VPABSD;
            break;

          case X86_INS_VPABSQ:
            tritonId = triton::arch::x86::ID_INS_VPABSQ;
            break;

          case X86_INS_VPABSW:
            tritonId = triton::arch::x86::ID_INS_VPABSW;
            break;

          case X86_INS_VPACKSSDW:
            tritonId = triton::arch::x86::ID_INS_VPACKSSDW;
            break;

          case X86_INS_VPACKSSWB:
            tritonId = triton::arch::x86::ID_INS_VPACKSSWB;
            break;

          case X86_INS_VPACKUSDW:
            tritonId = triton::arch::x86::ID_INS_VPACKUSDW;
            break;

          case X86_INS_VPACKUSWB:
            tritonId = triton::arch::x86::ID_INS_VPACKUSWB;
            break;

          case X86_INS_VPADDB:
            tritonId = triton::arch::x86::ID_INS_VPADDB;
            break;

          case X86_INS_VPADDD:
            tritonId = triton::arch::x86::ID_INS_VPADDD;
            break;

          case X86_INS_VPADDQ:
            tritonId = triton::arch::x86::ID_INS_VPADDQ;
            break;

          case X86_INS_VPADDSB:
            tritonId = triton::arch::x86::ID_INS_VPADDSB;
            break;

          case X86_INS_VPADDSW:
            tritonId = triton::arch::x86::ID_INS_VPADDSW;
            break;

          case X86_INS_VPADDUSB:
            tritonId = triton::arch::x86::ID_INS_VPADDUSB;
            break;

          case X86_INS_VPADDUSW:
            tritonId = triton::arch::x86::ID_INS_VPADDUSW;
            break;

          case X86_INS_VPADDW:
            tritonId = triton::arch::x86::ID_INS_VPADDW;
            break;

          case X86_INS_VPALIGNR:
            tritonId = triton::arch::x86::ID_INS_VPALIGNR;
            break;

          case X86_INS_VPANDD:
            tritonId = triton::arch::x86::ID_INS_VPANDD;
            break;

          case X86_INS_VPANDND:
            tritonId = triton::arch::x86::ID_INS_VPANDND;
            break;

          case X86_INS_VPANDNQ:
            tritonId = triton::arch::x86::ID_INS_VPANDNQ;
            break;

          case X86_INS_VPANDN:
            tritonId = triton::arch::x86::ID_INS_VPANDN;
            break;

          case X86_INS_VPANDQ:
            tritonId = triton::arch::x86::ID_INS_VPANDQ;
            break;

          case X86_INS_VPAND:
            tritonId = triton::arch::x86::ID_INS_VPAND;
            break;

          case X86_INS_VPAVGB:
            tritonId = triton::arch::x86::ID_INS_VPAVGB;
            break;

          case X86_INS_VPAVGW:
            tritonId = triton::arch::x86::ID_INS_VPAVGW;
            break;

          case X86_INS_VPBLENDD:
            tritonId = triton::arch::x86::ID_INS_VPBLENDD;
            break;

          case X86_INS_VPBLENDMD:
            tritonId = triton::arch::x86::ID_INS_VPBLENDMD;
            break;

          case X86_INS_VPBLENDMQ:
            tritonId = triton::arch::x86::ID_INS_VPBLENDMQ;
            break;

          case X86_INS_VPBLENDVB:
            tritonId = triton::arch::x86::ID_INS_VPBLENDVB;
            break;

          case X86_INS_VPBLENDW:
            tritonId = triton::arch::x86::ID_INS_VPBLENDW;
            break;

          case X86_INS_VPBROADCASTB:
            tritonId = triton::arch::x86::ID_INS_VPBROADCASTB;
            break;

          case X86_INS_VPBROADCASTD:
            tritonId = triton::arch::x86::ID_INS_VPBROADCASTD;
            break;

          case X86_INS_VPBROADCASTMB2Q:
            tritonId = triton::arch::x86::ID_INS_VPBROADCASTMB2Q;
            break;

          case X86_INS_VPBROADCASTMW2D:
            tritonId = triton::arch::x86::ID_INS_VPBROADCASTMW2D;
            break;

          case X86_INS_VPBROADCASTQ:
            tritonId = triton::arch::x86::ID_INS_VPBROADCASTQ;
            break;

          case X86_INS_VPBROADCASTW:
            tritonId = triton::arch::x86::ID_INS_VPBROADCASTW;
            break;

          case X86_INS_VPCLMULQDQ:
            tritonId = triton::arch::x86::ID_INS_VPCLMULQDQ;
            break;

          case X86_INS_VPCMOV:
            tritonId = triton::arch::x86::ID_INS_VPCMOV;
            break;

          case X86_INS_VPCMP:
            tritonId = triton::arch::x86::ID_INS_VPCMP;
            break;

          case X86_INS_VPCMPD:
            tritonId = triton::arch::x86::ID_INS_VPCMPD;
            break;

          case X86_INS_VPCMPEQB:
            tritonId = triton::arch::x86::ID_INS_VPCMPEQB;
            break;

          case X86_INS_VPCMPEQD:
            tritonId = triton::arch::x86::ID_INS_VPCMPEQD;
            break;

          case X86_INS_VPCMPEQQ:
            tritonId = triton::arch::x86::ID_INS_VPCMPEQQ;
            break;

          case X86_INS_VPCMPEQW:
            tritonId = triton::arch::x86::ID_INS_VPCMPEQW;
            break;

          case X86_INS_VPCMPESTRI:
            tritonId = triton::arch::x86::ID_INS_VPCMPESTRI;
            break;

          case X86_INS_VPCMPESTRM:
            tritonId = triton::arch::x86::ID_INS_VPCMPESTRM;
            break;

          case X86_INS_VPCMPGTB:
            tritonId = triton::arch::x86::ID_INS_VPCMPGTB;
            break;

          case X86_INS_VPCMPGTD:
            tritonId = triton::arch::x86::ID_INS_VPCMPGTD;
            break;

          case X86_INS_VPCMPGTQ:
            tritonId = triton::arch::x86::ID_INS_VPCMPGTQ;
            break;

          case X86_INS_VPCMPGTW:
            tritonId = triton::arch::x86::ID_INS_VPCMPGTW;
            break;

          case X86_INS_VPCMPISTRI:
            tritonId = triton::arch::x86::ID_INS_VPCMPISTRI;
            break;

          case X86_INS_VPCMPISTRM:
            tritonId = triton::arch::x86::ID_INS_VPCMPISTRM;
            break;

          case X86_INS_VPCMPQ:
            tritonId = triton::arch::x86::ID_INS_VPCMPQ;
            break;

          case X86_INS_VPCMPUD:
            tritonId = triton::arch::x86::ID_INS_VPCMPUD;
            break;

          case X86_INS_VPCMPUQ:
            tritonId = triton::arch::x86::ID_INS_VPCMPUQ;
            break;

          case X86_INS_VPCOMB:
            tritonId = triton::arch::x86::ID_INS_VPCOMB;
            break;

          case X86_INS_VPCOMD:
            tritonId = triton::arch::x86::ID_INS_VPCOMD;
            break;

          case X86_INS_VPCOMQ:
            tritonId = triton::arch::x86::ID_INS_VPCOMQ;
            break;

          case X86_INS_VPCOMUB:
            tritonId = triton::arch::x86::ID_INS_VPCOMUB;
            break;

          case X86_INS_VPCOMUD:
            tritonId = triton::arch::x86::ID_INS_VPCOMUD;
            break;

          case X86_INS_VPCOMUQ:
            tritonId = triton::arch::x86::ID_INS_VPCOMUQ;
            break;

          case X86_INS_VPCOMUW:
            tritonId = triton::arch::x86::ID_INS_VPCOMUW;
            break;

          case X86_INS_VPCOMW:
            tritonId = triton::arch::x86::ID_INS_VPCOMW;
            break;

          case X86_INS_VPCONFLICTD:
            tritonId = triton::arch::x86::ID_INS_VPCONFLICTD;
            break;

          case X86_INS_VPCONFLICTQ:
            tritonId = triton::arch::x86::ID_INS_VPCONFLICTQ;
            break;

          case X86_INS_VPERM2F128:
            tritonId = triton::arch::x86::ID_INS_VPERM2F128;
            break;

          case X86_INS_VPERM2I128:
            tritonId = triton::arch::x86::ID_INS_VPERM2I128;
            break;

          case X86_INS_VPERMD:
            tritonId = triton::arch::x86::ID_INS_VPERMD;
            break;

          case X86_INS_VPERMI2D:
            tritonId = triton::arch::x86::ID_INS_VPERMI2D;
            break;

          case X86_INS_VPERMI2PD:
            tritonId = triton::arch::x86::ID_INS_VPERMI2PD;
            break;

          case X86_INS_VPERMI2PS:
            tritonId = triton::arch::x86::ID_INS_VPERMI2PS;
            break;

          case X86_INS_VPERMI2Q:
            tritonId = triton::arch::x86::ID_INS_VPERMI2Q;
            break;

          case X86_INS_VPERMIL2PD:
            tritonId = triton::arch::x86::ID_INS_VPERMIL2PD;
            break;

          case X86_INS_VPERMIL2PS:
            tritonId = triton::arch::x86::ID_INS_VPERMIL2PS;
            break;

          case X86_INS_VPERMILPD:
            tritonId = triton::arch::x86::ID_INS_VPERMILPD;
            break;

          case X86_INS_VPERMILPS:
            tritonId = triton::arch::x86::ID_INS_VPERMILPS;
            break;

          case X86_INS_VPERMPD:
            tritonId = triton::arch::x86::ID_INS_VPERMPD;
            break;

          case X86_INS_VPERMPS:
            tritonId = triton::arch::x86::ID_INS_VPERMPS;
            break;

          case X86_INS_VPERMQ:
            tritonId = triton::arch::x86::ID_INS_VPERMQ;
            break;

          case X86_INS_VPERMT2D:
            tritonId = triton::arch::x86::ID_INS_VPERMT2D;
            break;

          case X86_INS_VPERMT2PD:
            tritonId = triton::arch::x86::ID_INS_VPERMT2PD;
            break;

          case X86_INS_VPERMT2PS:
            tritonId = triton::arch::x86::ID_INS_VPERMT2PS;
            break;

          case X86_INS_VPERMT2Q:
            tritonId = triton::arch::x86::ID_INS_VPERMT2Q;
            break;

          case X86_INS_VPEXTRB:
            tritonId = triton::arch::x86::ID_INS_VPEXTRB;
            break;

          case X86_INS_VPEXTRD:
            tritonId = triton::arch::x86::ID_INS_VPEXTRD;
            break;

          case X86_INS_VPEXTRQ:
            tritonId = triton::arch::x86::ID_INS_VPEXTRQ;
            break;

          case X86_INS_VPEXTRW:
            tritonId = triton::arch::x86::ID_INS_VPEXTRW;
            break;

          case X86_INS_VPGATHERDD:
            tritonId = triton::arch::x86::ID_INS_VPGATHERDD;
            break;

          case X86_INS_VPGATHERDQ:
            tritonId = triton::arch::x86::ID_INS_VPGATHERDQ;
            break;

          case X86_INS_VPGATHERQD:
            tritonId = triton::arch::x86::ID_INS_VPGATHERQD;
            break;

          case X86_INS_VPGATHERQQ:
            tritonId = triton::arch::x86::ID_INS_VPGATHERQQ;
            break;

          case X86_INS_VPHADDBD:
            tritonId = triton::arch::x86::ID_INS_VPHADDBD;
            break;

          case X86_INS_VPHADDBQ:
            tritonId = triton::arch::x86::ID_INS_VPHADDBQ;
            break;

          case X86_INS_VPHADDBW:
            tritonId = triton::arch::x86::ID_INS_VPHADDBW;
            break;

          case X86_INS_VPHADDDQ:
            tritonId = triton::arch::x86::ID_INS_VPHADDDQ;
            break;

          case X86_INS_VPHADDD:
            tritonId = triton::arch::x86::ID_INS_VPHADDD;
            break;

          case X86_INS_VPHADDSW:
            tritonId = triton::arch::x86::ID_INS_VPHADDSW;
            break;

          case X86_INS_VPHADDUBD:
            tritonId = triton::arch::x86::ID_INS_VPHADDUBD;
            break;

          case X86_INS_VPHADDUBQ:
            tritonId = triton::arch::x86::ID_INS_VPHADDUBQ;
            break;

          case X86_INS_VPHADDUBW:
            tritonId = triton::arch::x86::ID_INS_VPHADDUBW;
            break;

          case X86_INS_VPHADDUDQ:
            tritonId = triton::arch::x86::ID_INS_VPHADDUDQ;
            break;

          case X86_INS_VPHADDUWD:
            tritonId = triton::arch::x86::ID_INS_VPHADDUWD;
            break;

          case X86_INS_VPHADDUWQ:
            tritonId = triton::arch::x86::ID_INS_VPHADDUWQ;
            break;

          case X86_INS_VPHADDWD:
            tritonId = triton::arch::x86::ID_INS_VPHADDWD;
            break;

          case X86_INS_VPHADDWQ:
            tritonId = triton::arch::x86::ID_INS_VPHADDWQ;
            break;

          case X86_INS_VPHADDW:
            tritonId = triton::arch::x86::ID_INS_VPHADDW;
            break;

          case X86_INS_VPHMINPOSUW:
            tritonId = triton::arch::x86::ID_INS_VPHMINPOSUW;
            break;

          case X86_INS_VPHSUBBW:
            tritonId = triton::arch::x86::ID_INS_VPHSUBBW;
            break;

          case X86_INS_VPHSUBDQ:
            tritonId = triton::arch::x86::ID_INS_VPHSUBDQ;
            break;

          case X86_INS_VPHSUBD:
            tritonId = triton::arch::x86::ID_INS_VPHSUBD;
            break;

          case X86_INS_VPHSUBSW:
            tritonId = triton::arch::x86::ID_INS_VPHSUBSW;
            break;

          case X86_INS_VPHSUBWD:
            tritonId = triton::arch::x86::ID_INS_VPHSUBWD;
            break;

          case X86_INS_VPHSUBW:
            tritonId = triton::arch::x86::ID_INS_VPHSUBW;
            break;

          case X86_INS_VPINSRB:
            tritonId = triton::arch::x86::ID_INS_VPINSRB;
            break;

          case X86_INS_VPINSRD:
            tritonId = triton::arch::x86::ID_INS_VPINSRD;
            break;

          case X86_INS_VPINSRQ:
            tritonId = triton::arch::x86::ID_INS_VPINSRQ;
            break;

          case X86_INS_VPINSRW:
            tritonId = triton::arch::x86::ID_INS_VPINSRW;
            break;

          case X86_INS_VPLZCNTD:
            tritonId = triton::arch::x86::ID_INS_VPLZCNTD;
            break;

          case X86_INS_VPLZCNTQ:
            tritonId = triton::arch::x86::ID_INS_VPLZCNTQ;
            break;

          case X86_INS_VPMACSDD:
            tritonId = triton::arch::x86::ID_INS_VPMACSDD;
            break;

          case X86_INS_VPMACSDQH:
            tritonId = triton::arch::x86::ID_INS_VPMACSDQH;
            break;

          case X86_INS_VPMACSDQL:
            tritonId = triton::arch::x86::ID_INS_VPMACSDQL;
            break;

          case X86_INS_VPMACSSDD:
            tritonId = triton::arch::x86::ID_INS_VPMACSSDD;
            break;

          case X86_INS_VPMACSSDQH:
            tritonId = triton::arch::x86::ID_INS_VPMACSSDQH;
            break;

          case X86_INS_VPMACSSDQL:
            tritonId = triton::arch::x86::ID_INS_VPMACSSDQL;
            break;

          case X86_INS_VPMACSSWD:
            tritonId = triton::arch::x86::ID_INS_VPMACSSWD;
            break;

          case X86_INS_VPMACSSWW:
            tritonId = triton::arch::x86::ID_INS_VPMACSSWW;
            break;

          case X86_INS_VPMACSWD:
            tritonId = triton::arch::x86::ID_INS_VPMACSWD;
            break;

          case X86_INS_VPMACSWW:
            tritonId = triton::arch::x86::ID_INS_VPMACSWW;
            break;

          case X86_INS_VPMADCSSWD:
            tritonId = triton::arch::x86::ID_INS_VPMADCSSWD;
            break;

          case X86_INS_VPMADCSWD:
            tritonId = triton::arch::x86::ID_INS_VPMADCSWD;
            break;

          case X86_INS_VPMADDUBSW:
            tritonId = triton::arch::x86::ID_INS_VPMADDUBSW;
            break;

          case X86_INS_VPMADDWD:
            tritonId = triton::arch::x86::ID_INS_VPMADDWD;
            break;

          case X86_INS_VPMASKMOVD:
            tritonId = triton::arch::x86::ID_INS_VPMASKMOVD;
            break;

          case X86_INS_VPMASKMOVQ:
            tritonId = triton::arch::x86::ID_INS_VPMASKMOVQ;
            break;

          case X86_INS_VPMAXSB:
            tritonId = triton::arch::x86::ID_INS_VPMAXSB;
            break;

          case X86_INS_VPMAXSD:
            tritonId = triton::arch::x86::ID_INS_VPMAXSD;
            break;

          case X86_INS_VPMAXSQ:
            tritonId = triton::arch::x86::ID_INS_VPMAXSQ;
            break;

          case X86_INS_VPMAXSW:
            tritonId = triton::arch::x86::ID_INS_VPMAXSW;
            break;

          case X86_INS_VPMAXUB:
            tritonId = triton::arch::x86::ID_INS_VPMAXUB;
            break;

          case X86_INS_VPMAXUD:
            tritonId = triton::arch::x86::ID_INS_VPMAXUD;
            break;

          case X86_INS_VPMAXUQ:
            tritonId = triton::arch::x86::ID_INS_VPMAXUQ;
            break;

          case X86_INS_VPMAXUW:
            tritonId = triton::arch::x86::ID_INS_VPMAXUW;
            break;

          case X86_INS_VPMINSB:
            tritonId = triton::arch::x86::ID_INS_VPMINSB;
            break;

          case X86_INS_VPMINSD:
            tritonId = triton::arch::x86::ID_INS_VPMINSD;
            break;

          case X86_INS_VPMINSQ:
            tritonId = triton::arch::x86::ID_INS_VPMINSQ;
            break;

          case X86_INS_VPMINSW:
            tritonId = triton::arch::x86::ID_INS_VPMINSW;
            break;

          case X86_INS_VPMINUB:
            tritonId = triton::arch::x86::ID_INS_VPMINUB;
            break;

          case X86_INS_VPMINUD:
            tritonId = triton::arch::x86::ID_INS_VPMINUD;
            break;

          case X86_INS_VPMINUQ:
            tritonId = triton::arch::x86::ID_INS_VPMINUQ;
            break;

          case X86_INS_VPMINUW:
            tritonId = triton::arch::x86::ID_INS_VPMINUW;
            break;

          case X86_INS_VPMOVDB:
            tritonId = triton::arch::x86::ID_INS_VPMOVDB;
            break;

          case X86_INS_VPMOVDW:
            tritonId = triton::arch::x86::ID_INS_VPMOVDW;
            break;

          case X86_INS_VPMOVMSKB:
            tritonId = triton::arch::x86::ID_INS_VPMOVMSKB;
            break;

          case X86_INS_VPMOVQB:
            tritonId = triton::arch::x86::ID_INS_VPMOVQB;
            break;

          case X86_INS_VPMOVQD:
            tritonId = triton::arch::x86::ID_INS_VPMOVQD;
            break;

          case X86_INS_VPMOVQW:
            tritonId = triton::arch::x86::ID_INS_VPMOVQW;
            break;

          case X86_INS_VPMOVSDB:
            tritonId = triton::arch::x86::ID_INS_VPMOVSDB;
            break;

          case X86_INS_VPMOVSDW:
            tritonId = triton::arch::x86::ID_INS_VPMOVSDW;
            break;

          case X86_INS_VPMOVSQB:
            tritonId = triton::arch::x86::ID_INS_VPMOVSQB;
            break;

          case X86_INS_VPMOVSQD:
            tritonId = triton::arch::x86::ID_INS_VPMOVSQD;
            break;

          case X86_INS_VPMOVSQW:
            tritonId = triton::arch::x86::ID_INS_VPMOVSQW;
            break;

          case X86_INS_VPMOVSXBD:
            tritonId = triton::arch::x86::ID_INS_VPMOVSXBD;
            break;

          case X86_INS_VPMOVSXBQ:
            tritonId = triton::arch::x86::ID_INS_VPMOVSXBQ;
            break;

          case X86_INS_VPMOVSXBW:
            tritonId = triton::arch::x86::ID_INS_VPMOVSXBW;
            break;

          case X86_INS_VPMOVSXDQ:
            tritonId = triton::arch::x86::ID_INS_VPMOVSXDQ;
            break;

          case X86_INS_VPMOVSXWD:
            tritonId = triton::arch::x86::ID_INS_VPMOVSXWD;
            break;

          case X86_INS_VPMOVSXWQ:
            tritonId = triton::arch::x86::ID_INS_VPMOVSXWQ;
            break;

          case X86_INS_VPMOVUSDB:
            tritonId = triton::arch::x86::ID_INS_VPMOVUSDB;
            break;

          case X86_INS_VPMOVUSDW:
            tritonId = triton::arch::x86::ID_INS_VPMOVUSDW;
            break;

          case X86_INS_VPMOVUSQB:
            tritonId = triton::arch::x86::ID_INS_VPMOVUSQB;
            break;

          case X86_INS_VPMOVUSQD:
            tritonId = triton::arch::x86::ID_INS_VPMOVUSQD;
            break;

          case X86_INS_VPMOVUSQW:
            tritonId = triton::arch::x86::ID_INS_VPMOVUSQW;
            break;

          case X86_INS_VPMOVZXBD:
            tritonId = triton::arch::x86::ID_INS_VPMOVZXBD;
            break;

          case X86_INS_VPMOVZXBQ:
            tritonId = triton::arch::x86::ID_INS_VPMOVZXBQ;
            break;

          case X86_INS_VPMOVZXBW:
            tritonId = triton::arch::x86::ID_INS_VPMOVZXBW;
            break;

          case X86_INS_VPMOVZXDQ:
            tritonId = triton::arch::x86::ID_INS_VPMOVZXDQ;
            break;

          case X86_INS_VPMOVZXWD:
            tritonId = triton::arch::x86::ID_INS_VPMOVZXWD;
            break;

          case X86_INS_VPMOVZXWQ:
            tritonId = triton::arch::x86::ID_INS_VPMOVZXWQ;
            break;

          case X86_INS_VPMULDQ:
            tritonId = triton::arch::x86::ID_INS_VPMULDQ;
            break;

          case X86_INS_VPMULHRSW:
            tritonId = triton::arch::x86::ID_INS_VPMULHRSW;
            break;

          case X86_INS_VPMULHUW:
            tritonId = triton::arch::x86::ID_INS_VPMULHUW;
            break;

          case X86_INS_VPMULHW:
            tritonId = triton::arch::x86::ID_INS_VPMULHW;
            break;

          case X86_INS_VPMULLD:
            tritonId = triton::arch::x86::ID_INS_VPMULLD;
            break;

          case X86_INS_VPMULLW:
            tritonId = triton::arch::x86::ID_INS_VPMULLW;
            break;

          case X86_INS_VPMULUDQ:
            tritonId = triton::arch::x86::ID_INS_VPMULUDQ;
            break;

          case X86_INS_VPORD:
            tritonId = triton::arch::x86::ID_INS_VPORD;
            break;

          case X86_INS_VPORQ:
            tritonId = triton::arch::x86::ID_INS_VPORQ;
            break;

          case X86_INS_VPOR:
            tritonId = triton::arch::x86::ID_INS_VPOR;
            break;

          case X86_INS_VPPERM:
            tritonId = triton::arch::x86::ID_INS_VPPERM;
            break;

          case X86_INS_VPROTB:
            tritonId = triton::arch::x86::ID_INS_VPROTB;
            break;

          case X86_INS_VPROTD:
            tritonId = triton::arch::x86::ID_INS_VPROTD;
            break;

          case X86_INS_VPROTQ:
            tritonId = triton::arch::x86::ID_INS_VPROTQ;
            break;

          case X86_INS_VPROTW:
            tritonId = triton::arch::x86::ID_INS_VPROTW;
            break;

          case X86_INS_VPSADBW:
            tritonId = triton::arch::x86::ID_INS_VPSADBW;
            break;

          case X86_INS_VPSCATTERDD:
            tritonId = triton::arch::x86::ID_INS_VPSCATTERDD;
            break;

          case X86_INS_VPSCATTERDQ:
            tritonId = triton::arch::x86::ID_INS_VPSCATTERDQ;
            break;

          case X86_INS_VPSCATTERQD:
            tritonId = triton::arch::x86::ID_INS_VPSCATTERQD;
            break;

          case X86_INS_VPSCATTERQQ:
            tritonId = triton::arch::x86::ID_INS_VPSCATTERQQ;
            break;

          case X86_INS_VPSHAB:
            tritonId = triton::arch::x86::ID_INS_VPSHAB;
            break;

          case X86_INS_VPSHAD:
            tritonId = triton::arch::x86::ID_INS_VPSHAD;
            break;

          case X86_INS_VPSHAQ:
            tritonId = triton::arch::x86::ID_INS_VPSHAQ;
            break;

          case X86_INS_VPSHAW:
            tritonId = triton::arch::x86::ID_INS_VPSHAW;
            break;

          case X86_INS_VPSHLB:
            tritonId = triton::arch::x86::ID_INS_VPSHLB;
            break;

          case X86_INS_VPSHLD:
            tritonId = triton::arch::x86::ID_INS_VPSHLD;
            break;

          case X86_INS_VPSHLQ:
            tritonId = triton::arch::x86::ID_INS_VPSHLQ;
            break;

          case X86_INS_VPSHLW:
            tritonId = triton::arch::x86::ID_INS_VPSHLW;
            break;

          case X86_INS_VPSHUFB:
            tritonId = triton::arch::x86::ID_INS_VPSHUFB;
            break;

          case X86_INS_VPSHUFD:
            tritonId = triton::arch::x86::ID_INS_VPSHUFD;
            break;

          case X86_INS_VPSHUFHW:
            tritonId = triton::arch::x86::ID_INS_VPSHUFHW;
            break;

          case X86_INS_VPSHUFLW:
            tritonId = triton::arch::x86::ID_INS_VPSHUFLW;
            break;

          case X86_INS_VPSIGNB:
            tritonId = triton::arch::x86::ID_INS_VPSIGNB;
            break;

          case X86_INS_VPSIGND:
            tritonId = triton::arch::x86::ID_INS_VPSIGND;
            break;

          case X86_INS_VPSIGNW:
            tritonId = triton::arch::x86::ID_INS_VPSIGNW;
            break;

          case X86_INS_VPSLLDQ:
            tritonId = triton::arch::x86::ID_INS_VPSLLDQ;
            break;

          case X86_INS_VPSLLD:
            tritonId = triton::arch::x86::ID_INS_VPSLLD;
            break;

          case X86_INS_VPSLLQ:
            tritonId = triton::arch::x86::ID_INS_VPSLLQ;
            break;

          case X86_INS_VPSLLVD:
            tritonId = triton::arch::x86::ID_INS_VPSLLVD;
            break;

          case X86_INS_VPSLLVQ:
            tritonId = triton::arch::x86::ID_INS_VPSLLVQ;
            break;

          case X86_INS_VPSLLW:
            tritonId = triton::arch::x86::ID_INS_VPSLLW;
            break;

          case X86_INS_VPSRAD:
            tritonId = triton::arch::x86::ID_INS_VPSRAD;
            break;

          case X86_INS_VPSRAQ:
            tritonId = triton::arch::x86::ID_INS_VPSRAQ;
            break;

          case X86_INS_VPSRAVD:
            tritonId = triton::arch::x86::ID_INS_VPSRAVD;
            break;

          case X86_INS_VPSRAVQ:
            tritonId = triton::arch::x86::ID_INS_VPSRAVQ;
            break;

          case X86_INS_VPSRAW:
            tritonId = triton::arch::x86::ID_INS_VPSRAW;
            break;

          case X86_INS_VPSRLDQ:
            tritonId = triton::arch::x86::ID_INS_VPSRLDQ;
            break;

          case X86_INS_VPSRLD:
            tritonId = triton::arch::x86::ID_INS_VPSRLD;
            break;

          case X86_INS_VPSRLQ:
            tritonId = triton::arch::x86::ID_INS_VPSRLQ;
            break;

          case X86_INS_VPSRLVD:
            tritonId = triton::arch::x86::ID_INS_VPSRLVD;
            break;

          case X86_INS_VPSRLVQ:
            tritonId = triton::arch::x86::ID_INS_VPSRLVQ;
            break;

          case X86_INS_VPSRLW:
            tritonId = triton::arch::x86::ID_INS_VPSRLW;
            break;

          case X86_INS_VPSUBB:
            tritonId = triton::arch::x86::ID_INS_VPSUBB;
            break;

          case X86_INS_VPSUBD:
            tritonId = triton::arch::x86::ID_INS_VPSUBD;
            break;

          case X86_INS_VPSUBQ:
            tritonId = triton::arch::x86::ID_INS_VPSUBQ;
            break;

          case X86_INS_VPSUBSB:
            tritonId = triton::arch::x86::ID_INS_VPSUBSB;
            break;

          case X86_INS_VPSUBSW:
            tritonId = triton::arch::x86::ID_INS_VPSUBSW;
            break;

          case X86_INS_VPSUBUSB:
            tritonId = triton::arch::x86::ID_INS_VPSUBUSB;
            break;

          case X86_INS_VPSUBUSW:
            tritonId = triton::arch::x86::ID_INS_VPSUBUSW;
            break;

          case X86_INS_VPSUBW:
            tritonId = triton::arch::x86::ID_INS_VPSUBW;
            break;

          case X86_INS_VPTESTMD:
            tritonId = triton::arch::x86::ID_INS_VPTESTMD;
            break;

          case X86_INS_VPTESTMQ:
            tritonId = triton::arch::x86::ID_INS_VPTESTMQ;
            break;

          case X86_INS_VPTESTNMD:
            tritonId = triton::arch::x86::ID_INS_VPTESTNMD;
            break;

          case X86_INS_VPTESTNMQ:
            tritonId = triton::arch::x86::ID_INS_VPTESTNMQ;
            break;

          case X86_INS_VPTEST:
            tritonId = triton::arch::x86::ID_INS_VPTEST;
            break;

          case X86_INS_VPUNPCKHBW:
            tritonId = triton::arch::x86::ID_INS_VPUNPCKHBW;
            break;

          case X86_INS_VPUNPCKHDQ:
            tritonId = triton::arch::x86::ID_INS_VPUNPCKHDQ;
            break;

          case X86_INS_VPUNPCKHQDQ:
            tritonId = triton::arch::x86::ID_INS_VPUNPCKHQDQ;
            break;

          case X86_INS_VPUNPCKHWD:
            tritonId = triton::arch::x86::ID_INS_VPUNPCKHWD;
            break;

          case X86_INS_VPUNPCKLBW:
            tritonId = triton::arch::x86::ID_INS_VPUNPCKLBW;
            break;

          case X86_INS_VPUNPCKLDQ:
            tritonId = triton::arch::x86::ID_INS_VPUNPCKLDQ;
            break;

          case X86_INS_VPUNPCKLQDQ:
            tritonId = triton::arch::x86::ID_INS_VPUNPCKLQDQ;
            break;

          case X86_INS_VPUNPCKLWD:
            tritonId = triton::arch::x86::ID_INS_VPUNPCKLWD;
            break;

          case X86_INS_VPXORD:
            tritonId = triton::arch::x86::ID_INS_VPXORD;
            break;

          case X86_INS_VPXORQ:
            tritonId = triton::arch::x86::ID_INS_VPXORQ;
            break;

          case X86_INS_VPXOR:
            tritonId = triton::arch::x86::ID_INS_VPXOR;
            break;

          case X86_INS_VRCP14PD:
            tritonId = triton::arch::x86::ID_INS_VRCP14PD;
            break;

          case X86_INS_VRCP14PS:
            tritonId = triton::arch::x86::ID_INS_VRCP14PS;
            break;

          case X86_INS_VRCP14SD:
            tritonId = triton::arch::x86::ID_INS_VRCP14SD;
            break;

          case X86_INS_VRCP14SS:
            tritonId = triton::arch::x86::ID_INS_VRCP14SS;
            break;

          case X86_INS_VRCP28PD:
            tritonId = triton::arch::x86::ID_INS_VRCP28PD;
            break;

          case X86_INS_VRCP28PS:
            tritonId = triton::arch::x86::ID_INS_VRCP28PS;
            break;

          case X86_INS_VRCP28SD:
            tritonId = triton::arch::x86::ID_INS_VRCP28SD;
            break;

          case X86_INS_VRCP28SS:
            tritonId = triton::arch::x86::ID_INS_VRCP28SS;
            break;

          case X86_INS_VRCPPS:
            tritonId = triton::arch::x86::ID_INS_VRCPPS;
            break;

          case X86_INS_VRCPSS:
            tritonId = triton::arch::x86::ID_INS_VRCPSS;
            break;

          case X86_INS_VRNDSCALEPD:
            tritonId = triton::arch::x86::ID_INS_VRNDSCALEPD;
            break;

          case X86_INS_VRNDSCALEPS:
            tritonId = triton::arch::x86::ID_INS_VRNDSCALEPS;
            break;

          case X86_INS_VRNDSCALESD:
            tritonId = triton::arch::x86::ID_INS_VRNDSCALESD;
            break;

          case X86_INS_VRNDSCALESS:
            tritonId = triton::arch::x86::ID_INS_VRNDSCALESS;
            break;

          case X86_INS_VROUNDPD:
            tritonId = triton::arch::x86::ID_INS_VROUNDPD;
            break;

          case X86_INS_VROUNDPS:
            tritonId = triton::arch::x86::ID_INS_VROUNDPS;
            break;

          case X86_INS_VROUNDSD:
            tritonId = triton::arch::x86::ID_INS_VROUNDSD;
            break;

          case X86_INS_VROUNDSS:
            tritonId = triton::arch::x86::ID_INS_VROUNDSS;
            break;

          case X86_INS_VRSQRT14PD:
            tritonId = triton::arch::x86::ID_INS_VRSQRT14PD;
            break;

          case X86_INS_VRSQRT14PS:
            tritonId = triton::arch::x86::ID_INS_VRSQRT14PS;
            break;

          case X86_INS_VRSQRT14SD:
            tritonId = triton::arch::x86::ID_INS_VRSQRT14SD;
            break;

          case X86_INS_VRSQRT14SS:
            tritonId = triton::arch::x86::ID_INS_VRSQRT14SS;
            break;

          case X86_INS_VRSQRT28PD:
            tritonId = triton::arch::x86::ID_INS_VRSQRT28PD;
            break;

          case X86_INS_VRSQRT28PS:
            tritonId = triton::arch::x86::ID_INS_VRSQRT28PS;
            break;

          case X86_INS_VRSQRT28SD:
            tritonId = triton::arch::x86::ID_INS_VRSQRT28SD;
            break;

          case X86_INS_VRSQRT28SS:
            tritonId = triton::arch::x86::ID_INS_VRSQRT28SS;
            break;

          case X86_INS_VRSQRTPS:
            tritonId = triton::arch::x86::ID_INS_VRSQRTPS;
            break;

          case X86_INS_VRSQRTSS:
            tritonId = triton::arch::x86::ID_INS_VRSQRTSS;
            break;

          case X86_INS_VSCATTERDPD:
            tritonId = triton::arch::x86::ID_INS_VSCATTERDPD;
            break;

          case X86_INS_VSCATTERDPS:
            tritonId = triton::arch::x86::ID_INS_VSCATTERDPS;
            break;

          case X86_INS_VSCATTERPF0DPD:
            tritonId = triton::arch::x86::ID_INS_VSCATTERPF0DPD;
            break;

          case X86_INS_VSCATTERPF0DPS:
            tritonId = triton::arch::x86::ID_INS_VSCATTERPF0DPS;
            break;

          case X86_INS_VSCATTERPF0QPD:
            tritonId = triton::arch::x86::ID_INS_VSCATTERPF0QPD;
            break;

          case X86_INS_VSCATTERPF0QPS:
            tritonId = triton::arch::x86::ID_INS_VSCATTERPF0QPS;
            break;

          case X86_INS_VSCATTERPF1DPD:
            tritonId = triton::arch::x86::ID_INS_VSCATTERPF1DPD;
            break;

          case X86_INS_VSCATTERPF1DPS:
            tritonId = triton::arch::x86::ID_INS_VSCATTERPF1DPS;
            break;

          case X86_INS_VSCATTERPF1QPD:
            tritonId = triton::arch::x86::ID_INS_VSCATTERPF1QPD;
            break;

          case X86_INS_VSCATTERPF1QPS:
            tritonId = triton::arch::x86::ID_INS_VSCATTERPF1QPS;
            break;

          case X86_INS_VSCATTERQPD:
            tritonId = triton::arch::x86::ID_INS_VSCATTERQPD;
            break;

          case X86_INS_VSCATTERQPS:
            tritonId = triton::arch::x86::ID_INS_VSCATTERQPS;
            break;

          case X86_INS_VSHUFPD:
            tritonId = triton::arch::x86::ID_INS_VSHUFPD;
            break;

          case X86_INS_VSHUFPS:
            tritonId = triton::arch::x86::ID_INS_VSHUFPS;
            break;

          case X86_INS_VSQRTPD:
            tritonId = triton::arch::x86::ID_INS_VSQRTPD;
            break;

          case X86_INS_VSQRTPS:
            tritonId = triton::arch::x86::ID_INS_VSQRTPS;
            break;

          case X86_INS_VSQRTSD:
            tritonId = triton::arch::x86::ID_INS_VSQRTSD;
            break;

          case X86_INS_VSQRTSS:
            tritonId = triton::arch::x86::ID_INS_VSQRTSS;
            break;

          case X86_INS_VSTMXCSR:
            tritonId = triton::arch::x86::ID_INS_VSTMXCSR;
            break;

          case X86_INS_VSUBPD:
            tritonId = triton::arch::x86::ID_INS_VSUBPD;
            break;

          case X86_INS_VSUBPS:
            tritonId = triton::arch::x86::ID_INS_VSUBPS;
            break;

          case X86_INS_VSUBSD:
            tritonId = triton::arch::x86::ID_INS_VSUBSD;
            break;

          case X86_INS_VSUBSS:
            tritonId = triton::arch::x86::ID_INS_VSUBSS;
            break;

          case X86_INS_VTESTPD:
            tritonId = triton::arch::x86::ID_INS_VTESTPD;
            break;

          case X86_INS_VTESTPS:
            tritonId = triton::arch::x86::ID_INS_VTESTPS;
            break;

          case X86_INS_VUNPCKHPD:
            tritonId = triton::arch::x86::ID_INS_VUNPCKHPD;
            break;

          case X86_INS_VUNPCKHPS:
            tritonId = triton::arch::x86::ID_INS_VUNPCKHPS;
            break;

          case X86_INS_VUNPCKLPD:
            tritonId = triton::arch::x86::ID_INS_VUNPCKLPD;
            break;

          case X86_INS_VUNPCKLPS:
            tritonId = triton::arch::x86::ID_INS_VUNPCKLPS;
            break;

          case X86_INS_VZEROALL:
            tritonId = triton::arch::x86::ID_INS_VZEROALL;
            break;

          case X86_INS_VZEROUPPER:
            tritonId = triton::arch::x86::ID_INS_VZEROUPPER;
            break;

          case X86_INS_WAIT:
            tritonId = triton::arch::x86::ID_INS_WAIT;
            break;

          case X86_INS_WBINVD:
            tritonId = triton::arch::x86::ID_INS_WBINVD;
            break;

          case X86_INS_WRFSBASE:
            tritonId = triton::arch::x86::ID_INS_WRFSBASE;
            break;

          case X86_INS_WRGSBASE:
            tritonId = triton::arch::x86::ID_INS_WRGSBASE;
            break;

          case X86_INS_WRMSR:
            tritonId = triton::arch::x86::ID_INS_WRMSR;
            break;

          case X86_INS_XABORT:
            tritonId = triton::arch::x86::ID_INS_XABORT;
            break;

          case X86_INS_XACQUIRE:
            tritonId = triton::arch::x86::ID_INS_XACQUIRE;
            break;

          case X86_INS_XBEGIN:
            tritonId = triton::arch::x86::ID_INS_XBEGIN;
            break;

          case X86_INS_XCHG:
            tritonId = triton::arch::x86::ID_INS_XCHG;
            break;

          case X86_INS_FXCH:
            tritonId = triton::arch::x86::ID_INS_FXCH;
            break;

          case X86_INS_XCRYPTCBC:
            tritonId = triton::arch::x86::ID_INS_XCRYPTCBC;
            break;

          case X86_INS_XCRYPTCFB:
            tritonId = triton::arch::x86::ID_INS_XCRYPTCFB;
            break;

          case X86_INS_XCRYPTCTR:
            tritonId = triton::arch::x86::ID_INS_XCRYPTCTR;
            break;

          case X86_INS_XCRYPTECB:
            tritonId = triton::arch::x86::ID_INS_XCRYPTECB;
            break;

          case X86_INS_XCRYPTOFB:
            tritonId = triton::arch::x86::ID_INS_XCRYPTOFB;
            break;

          case X86_INS_XEND:
            tritonId = triton::arch::x86::ID_INS_XEND;
            break;

          case X86_INS_XGETBV:
            tritonId = triton::arch::x86::ID_INS_XGETBV;
            break;

          case X86_INS_XLATB:
            tritonId = triton::arch::x86::ID_INS_XLATB;
            break;

          case X86_INS_XRELEASE:
            tritonId = triton::arch::x86::ID_INS_XRELEASE;
            break;

          case X86_INS_XRSTOR:
            tritonId = triton::arch::x86::ID_INS_XRSTOR;
            break;

          case X86_INS_XRSTOR64:
            tritonId = triton::arch::x86::ID_INS_XRSTOR64;
            break;

          case X86_INS_XSAVE:
            tritonId = triton::arch::x86::ID_INS_XSAVE;
            break;

          case X86_INS_XSAVE64:
            tritonId = triton::arch::x86::ID_INS_XSAVE64;
            break;

          case X86_INS_XSAVEOPT:
            tritonId = triton::arch::x86::ID_INS_XSAVEOPT;
            break;

          case X86_INS_XSAVEOPT64:
            tritonId = triton::arch::x86::ID_INS_XSAVEOPT64;
            break;

          case X86_INS_XSETBV:
            tritonId = triton::arch::x86::ID_INS_XSETBV;
            break;

          case X86_INS_XSHA1:
            tritonId = triton::arch::x86::ID_INS_XSHA1;
            break;

          case X86_INS_XSHA256:
            tritonId = triton::arch::x86::ID_INS_XSHA256;
            break;

          case X86_INS_XSTORE:
            tritonId = triton::arch::x86::ID_INS_XSTORE;
            break;

          case X86_INS_XTEST:
            tritonId = triton::arch::x86::ID_INS_XTEST;
            break;

          default:
            tritonId = triton::arch::x86::ID_INST_INVALID;
            break;

        }
        return tritonId;
      }


    }; /* x86 namespace */
  }; /* arch namespace */
}; /* triton namespace */

