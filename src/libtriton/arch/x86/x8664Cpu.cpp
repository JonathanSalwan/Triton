//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstring>

#include <api.hpp>
#include <architecture.hpp>
#include <callbacks.hpp>
#include <coreUtils.hpp>
#include <cpuSize.hpp>
#include <exceptions.hpp>
#include <externalLibs.hpp>
#include <immediate.hpp>
#include <x8664Cpu.hpp>
#include <x86Specifications.hpp>

#ifdef TRITON_PYTHON_BINDINGS
  #include <pythonBindings.hpp>
#endif



namespace triton {
  namespace arch {
    namespace x86 {

      x8664Cpu::x8664Cpu() {
        this->clear();
      }


      x8664Cpu::x8664Cpu(const x8664Cpu& other) {
        this->copy(other);
      }


      x8664Cpu::~x8664Cpu() {
        this->memory.clear();
      }


      void x8664Cpu::copy(const x8664Cpu& other) {
        this->memory = other.memory;
        memcpy(this->rax,     other.rax,    sizeof(this->rax));
        memcpy(this->rbx,     other.rbx,    sizeof(this->rbx));
        memcpy(this->rcx,     other.rcx,    sizeof(this->rcx));
        memcpy(this->rdx,     other.rdx,    sizeof(this->rdx));
        memcpy(this->rdi,     other.rdi,    sizeof(this->rdi));
        memcpy(this->rsi,     other.rsi,    sizeof(this->rsi));
        memcpy(this->rsp,     other.rsp,    sizeof(this->rsp));
        memcpy(this->rbp,     other.rbp,    sizeof(this->rbp));
        memcpy(this->rip,     other.rip,    sizeof(this->rip));
        memcpy(this->eflags,  other.eflags, sizeof(this->eflags));
        memcpy(this->r8,      other.r8,     sizeof(this->r8));
        memcpy(this->r9,      other.r9,     sizeof(this->r9));
        memcpy(this->r10,     other.r10,    sizeof(this->r10));
        memcpy(this->r11,     other.r11,    sizeof(this->r11));
        memcpy(this->r12,     other.r12,    sizeof(this->r12));
        memcpy(this->r13,     other.r13,    sizeof(this->r13));
        memcpy(this->r14,     other.r14,    sizeof(this->r14));
        memcpy(this->r15,     other.r15,    sizeof(this->r15));
        memcpy(this->mm0,     other.mm0,    sizeof(this->mm0));
        memcpy(this->mm1,     other.mm1,    sizeof(this->mm1));
        memcpy(this->mm2,     other.mm2,    sizeof(this->mm2));
        memcpy(this->mm3,     other.mm3,    sizeof(this->mm3));
        memcpy(this->mm4,     other.mm4,    sizeof(this->mm4));
        memcpy(this->mm5,     other.mm5,    sizeof(this->mm5));
        memcpy(this->mm6,     other.mm6,    sizeof(this->mm6));
        memcpy(this->mm7,     other.mm7,    sizeof(this->mm7));
        memcpy(this->xmm0,    other.xmm0,   sizeof(this->xmm0));
        memcpy(this->xmm1,    other.xmm1,   sizeof(this->xmm1));
        memcpy(this->xmm2,    other.xmm2,   sizeof(this->xmm2));
        memcpy(this->xmm3,    other.xmm3,   sizeof(this->xmm3));
        memcpy(this->xmm4,    other.xmm4,   sizeof(this->xmm4));
        memcpy(this->xmm5,    other.xmm5,   sizeof(this->xmm5));
        memcpy(this->xmm6,    other.xmm6,   sizeof(this->xmm6));
        memcpy(this->xmm7,    other.xmm7,   sizeof(this->xmm7));
        memcpy(this->xmm8,    other.xmm8,   sizeof(this->xmm8));
        memcpy(this->xmm9,    other.xmm9,   sizeof(this->xmm9));
        memcpy(this->xmm10,   other.xmm10,  sizeof(this->xmm10));
        memcpy(this->xmm11,   other.xmm11,  sizeof(this->xmm11));
        memcpy(this->xmm12,   other.xmm12,  sizeof(this->xmm12));
        memcpy(this->xmm13,   other.xmm13,  sizeof(this->xmm13));
        memcpy(this->xmm14,   other.xmm14,  sizeof(this->xmm14));
        memcpy(this->xmm15,   other.xmm15,  sizeof(this->xmm15));
        memcpy(this->ymm0,    other.ymm0,   sizeof(this->ymm0));
        memcpy(this->ymm1,    other.ymm1,   sizeof(this->ymm1));
        memcpy(this->ymm2,    other.ymm2,   sizeof(this->ymm2));
        memcpy(this->ymm3,    other.ymm3,   sizeof(this->ymm3));
        memcpy(this->ymm4,    other.ymm4,   sizeof(this->ymm4));
        memcpy(this->ymm5,    other.ymm5,   sizeof(this->ymm5));
        memcpy(this->ymm6,    other.ymm6,   sizeof(this->ymm6));
        memcpy(this->ymm7,    other.ymm7,   sizeof(this->ymm7));
        memcpy(this->ymm8,    other.ymm8,   sizeof(this->ymm8));
        memcpy(this->ymm9,    other.ymm9,   sizeof(this->ymm9));
        memcpy(this->ymm10,   other.ymm10,  sizeof(this->ymm10));
        memcpy(this->ymm11,   other.ymm11,  sizeof(this->ymm11));
        memcpy(this->ymm12,   other.ymm12,  sizeof(this->ymm12));
        memcpy(this->ymm13,   other.ymm13,  sizeof(this->ymm13));
        memcpy(this->ymm14,   other.ymm14,  sizeof(this->ymm14));
        memcpy(this->ymm15,   other.ymm15,  sizeof(this->ymm15));
        memcpy(this->zmm0,    other.zmm0,   sizeof(this->zmm0));
        memcpy(this->zmm1,    other.zmm1,   sizeof(this->zmm1));
        memcpy(this->zmm2,    other.zmm2,   sizeof(this->zmm2));
        memcpy(this->zmm3,    other.zmm3,   sizeof(this->zmm3));
        memcpy(this->zmm4,    other.zmm4,   sizeof(this->zmm4));
        memcpy(this->zmm5,    other.zmm5,   sizeof(this->zmm5));
        memcpy(this->zmm6,    other.zmm6,   sizeof(this->zmm6));
        memcpy(this->zmm7,    other.zmm7,   sizeof(this->zmm7));
        memcpy(this->zmm8,    other.zmm8,   sizeof(this->zmm8));
        memcpy(this->zmm9,    other.zmm9,   sizeof(this->zmm9));
        memcpy(this->zmm10,   other.zmm10,  sizeof(this->zmm10));
        memcpy(this->zmm11,   other.zmm11,  sizeof(this->zmm11));
        memcpy(this->zmm12,   other.zmm12,  sizeof(this->zmm12));
        memcpy(this->zmm13,   other.zmm13,  sizeof(this->zmm13));
        memcpy(this->zmm14,   other.zmm14,  sizeof(this->zmm14));
        memcpy(this->zmm15,   other.zmm15,  sizeof(this->zmm15));
        memcpy(this->zmm16,   other.zmm16,  sizeof(this->zmm16));
        memcpy(this->zmm17,   other.zmm17,  sizeof(this->zmm17));
        memcpy(this->zmm18,   other.zmm18,  sizeof(this->zmm18));
        memcpy(this->zmm19,   other.zmm19,  sizeof(this->zmm19));
        memcpy(this->zmm20,   other.zmm20,  sizeof(this->zmm20));
        memcpy(this->zmm21,   other.zmm21,  sizeof(this->zmm21));
        memcpy(this->zmm22,   other.zmm22,  sizeof(this->zmm22));
        memcpy(this->zmm23,   other.zmm23,  sizeof(this->zmm23));
        memcpy(this->zmm24,   other.zmm24,  sizeof(this->zmm24));
        memcpy(this->zmm25,   other.zmm25,  sizeof(this->zmm25));
        memcpy(this->zmm26,   other.zmm26,  sizeof(this->zmm26));
        memcpy(this->zmm27,   other.zmm27,  sizeof(this->zmm27));
        memcpy(this->zmm28,   other.zmm28,  sizeof(this->zmm28));
        memcpy(this->zmm29,   other.zmm29,  sizeof(this->zmm29));
        memcpy(this->zmm30,   other.zmm30,  sizeof(this->zmm30));
        memcpy(this->zmm31,   other.zmm31,  sizeof(this->zmm31));
        memcpy(this->mxcsr,   other.mxcsr,  sizeof(this->mxcsr));
        memcpy(this->cr0,     other.cr0,    sizeof(this->cr0));
        memcpy(this->cr1,     other.cr1,    sizeof(this->cr1));
        memcpy(this->cr2,     other.cr2,    sizeof(this->cr2));
        memcpy(this->cr3,     other.cr3,    sizeof(this->cr3));
        memcpy(this->cr4,     other.cr4,    sizeof(this->cr4));
        memcpy(this->cr5,     other.cr5,    sizeof(this->cr5));
        memcpy(this->cr6,     other.cr6,    sizeof(this->cr6));
        memcpy(this->cr7,     other.cr7,    sizeof(this->cr7));
        memcpy(this->cr8,     other.cr8,    sizeof(this->cr8));
        memcpy(this->cr9,     other.cr9,    sizeof(this->cr9));
        memcpy(this->cr10,    other.cr10,   sizeof(this->cr10));
        memcpy(this->cr11,    other.cr11,   sizeof(this->cr11));
        memcpy(this->cr12,    other.cr12,   sizeof(this->cr12));
        memcpy(this->cr13,    other.cr13,   sizeof(this->cr13));
        memcpy(this->cr14,    other.cr14,   sizeof(this->cr14));
        memcpy(this->cr15,    other.cr15,   sizeof(this->cr15));
        memcpy(this->cs,      other.cs,     sizeof(this->cs));
        memcpy(this->ds,      other.ds,     sizeof(this->ds));
        memcpy(this->es,      other.es,     sizeof(this->es));
        memcpy(this->fs,      other.fs,     sizeof(this->fs));
        memcpy(this->gs,      other.gs,     sizeof(this->gs));
        memcpy(this->ss,      other.ss,     sizeof(this->ss));
      }


      void x8664Cpu::init(void) {
        /* Define registers ========================================================= */
        triton::arch::x86::x86_reg_rax    = triton::arch::Register(triton::arch::x86::ID_REG_RAX);
        triton::arch::x86::x86_reg_eax    = triton::arch::Register(triton::arch::x86::ID_REG_EAX);
        triton::arch::x86::x86_reg_ax     = triton::arch::Register(triton::arch::x86::ID_REG_AX);
        triton::arch::x86::x86_reg_ah     = triton::arch::Register(triton::arch::x86::ID_REG_AH);
        triton::arch::x86::x86_reg_al     = triton::arch::Register(triton::arch::x86::ID_REG_AL);

        triton::arch::x86::x86_reg_rbx    = triton::arch::Register(triton::arch::x86::ID_REG_RBX);
        triton::arch::x86::x86_reg_ebx    = triton::arch::Register(triton::arch::x86::ID_REG_EBX);
        triton::arch::x86::x86_reg_bx     = triton::arch::Register(triton::arch::x86::ID_REG_BX);
        triton::arch::x86::x86_reg_bh     = triton::arch::Register(triton::arch::x86::ID_REG_BH);
        triton::arch::x86::x86_reg_bl     = triton::arch::Register(triton::arch::x86::ID_REG_BL);

        triton::arch::x86::x86_reg_rcx    = triton::arch::Register(triton::arch::x86::ID_REG_RCX);
        triton::arch::x86::x86_reg_ecx    = triton::arch::Register(triton::arch::x86::ID_REG_ECX);
        triton::arch::x86::x86_reg_cx     = triton::arch::Register(triton::arch::x86::ID_REG_CX);
        triton::arch::x86::x86_reg_ch     = triton::arch::Register(triton::arch::x86::ID_REG_CH);
        triton::arch::x86::x86_reg_cl     = triton::arch::Register(triton::arch::x86::ID_REG_CL);

        triton::arch::x86::x86_reg_rdx    = triton::arch::Register(triton::arch::x86::ID_REG_RDX);
        triton::arch::x86::x86_reg_edx    = triton::arch::Register(triton::arch::x86::ID_REG_EDX);
        triton::arch::x86::x86_reg_dx     = triton::arch::Register(triton::arch::x86::ID_REG_DX);
        triton::arch::x86::x86_reg_dh     = triton::arch::Register(triton::arch::x86::ID_REG_DH);
        triton::arch::x86::x86_reg_dl     = triton::arch::Register(triton::arch::x86::ID_REG_DL);

        triton::arch::x86::x86_reg_rdi    = triton::arch::Register(triton::arch::x86::ID_REG_RDI);
        triton::arch::x86::x86_reg_edi    = triton::arch::Register(triton::arch::x86::ID_REG_EDI);
        triton::arch::x86::x86_reg_di     = triton::arch::Register(triton::arch::x86::ID_REG_DI);
        triton::arch::x86::x86_reg_dil    = triton::arch::Register(triton::arch::x86::ID_REG_DIL);

        triton::arch::x86::x86_reg_rsi    = triton::arch::Register(triton::arch::x86::ID_REG_RSI);
        triton::arch::x86::x86_reg_esi    = triton::arch::Register(triton::arch::x86::ID_REG_ESI);
        triton::arch::x86::x86_reg_si     = triton::arch::Register(triton::arch::x86::ID_REG_SI);
        triton::arch::x86::x86_reg_sil    = triton::arch::Register(triton::arch::x86::ID_REG_SIL);

        triton::arch::x86::x86_reg_rsp    = triton::arch::Register(triton::arch::x86::ID_REG_RSP);
        triton::arch::x86::x86_reg_esp    = triton::arch::Register(triton::arch::x86::ID_REG_ESP);
        triton::arch::x86::x86_reg_sp     = triton::arch::Register(triton::arch::x86::ID_REG_SP);
        triton::arch::x86::x86_reg_spl    = triton::arch::Register(triton::arch::x86::ID_REG_SPL);
        triton::arch::x86::x86_reg_stack  = triton::arch::Register(triton::arch::x86::ID_REG_RSP);

        triton::arch::x86::x86_reg_rbp    = triton::arch::Register(triton::arch::x86::ID_REG_RBP);
        triton::arch::x86::x86_reg_ebp    = triton::arch::Register(triton::arch::x86::ID_REG_EBP);
        triton::arch::x86::x86_reg_bp     = triton::arch::Register(triton::arch::x86::ID_REG_BP);
        triton::arch::x86::x86_reg_bpl    = triton::arch::Register(triton::arch::x86::ID_REG_BPL);

        triton::arch::x86::x86_reg_rip    = triton::arch::Register(triton::arch::x86::ID_REG_RIP);
        triton::arch::x86::x86_reg_eip    = triton::arch::Register(triton::arch::x86::ID_REG_EIP);
        triton::arch::x86::x86_reg_ip     = triton::arch::Register(triton::arch::x86::ID_REG_IP);
        triton::arch::x86::x86_reg_pc     = triton::arch::Register(triton::arch::x86::ID_REG_RIP);

        triton::arch::x86::x86_reg_eflags = triton::arch::Register(triton::arch::x86::ID_REG_EFLAGS);

        triton::arch::x86::x86_reg_r8     = triton::arch::Register(triton::arch::x86::ID_REG_R8);
        triton::arch::x86::x86_reg_r8d    = triton::arch::Register(triton::arch::x86::ID_REG_R8D);
        triton::arch::x86::x86_reg_r8w    = triton::arch::Register(triton::arch::x86::ID_REG_R8W);
        triton::arch::x86::x86_reg_r8b    = triton::arch::Register(triton::arch::x86::ID_REG_R8B);

        triton::arch::x86::x86_reg_r9     = triton::arch::Register(triton::arch::x86::ID_REG_R9);
        triton::arch::x86::x86_reg_r9d    = triton::arch::Register(triton::arch::x86::ID_REG_R9D);
        triton::arch::x86::x86_reg_r9w    = triton::arch::Register(triton::arch::x86::ID_REG_R9W);
        triton::arch::x86::x86_reg_r9b    = triton::arch::Register(triton::arch::x86::ID_REG_R9B);

        triton::arch::x86::x86_reg_r10    = triton::arch::Register(triton::arch::x86::ID_REG_R10);
        triton::arch::x86::x86_reg_r10d   = triton::arch::Register(triton::arch::x86::ID_REG_R10D);
        triton::arch::x86::x86_reg_r10w   = triton::arch::Register(triton::arch::x86::ID_REG_R10W);
        triton::arch::x86::x86_reg_r10b   = triton::arch::Register(triton::arch::x86::ID_REG_R10B);

        triton::arch::x86::x86_reg_r11    = triton::arch::Register(triton::arch::x86::ID_REG_R11);
        triton::arch::x86::x86_reg_r11d   = triton::arch::Register(triton::arch::x86::ID_REG_R11D);
        triton::arch::x86::x86_reg_r11w   = triton::arch::Register(triton::arch::x86::ID_REG_R11W);
        triton::arch::x86::x86_reg_r11b   = triton::arch::Register(triton::arch::x86::ID_REG_R11B);

        triton::arch::x86::x86_reg_r12    = triton::arch::Register(triton::arch::x86::ID_REG_R12);
        triton::arch::x86::x86_reg_r12d   = triton::arch::Register(triton::arch::x86::ID_REG_R12D);
        triton::arch::x86::x86_reg_r12w   = triton::arch::Register(triton::arch::x86::ID_REG_R12W);
        triton::arch::x86::x86_reg_r12b   = triton::arch::Register(triton::arch::x86::ID_REG_R12B);

        triton::arch::x86::x86_reg_r13    = triton::arch::Register(triton::arch::x86::ID_REG_R13);
        triton::arch::x86::x86_reg_r13d   = triton::arch::Register(triton::arch::x86::ID_REG_R13D);
        triton::arch::x86::x86_reg_r13w   = triton::arch::Register(triton::arch::x86::ID_REG_R13W);
        triton::arch::x86::x86_reg_r13b   = triton::arch::Register(triton::arch::x86::ID_REG_R13B);

        triton::arch::x86::x86_reg_r14    = triton::arch::Register(triton::arch::x86::ID_REG_R14);
        triton::arch::x86::x86_reg_r14d   = triton::arch::Register(triton::arch::x86::ID_REG_R14D);
        triton::arch::x86::x86_reg_r14w   = triton::arch::Register(triton::arch::x86::ID_REG_R14W);
        triton::arch::x86::x86_reg_r14b   = triton::arch::Register(triton::arch::x86::ID_REG_R14B);

        triton::arch::x86::x86_reg_r15    = triton::arch::Register(triton::arch::x86::ID_REG_R15);
        triton::arch::x86::x86_reg_r15d   = triton::arch::Register(triton::arch::x86::ID_REG_R15D);
        triton::arch::x86::x86_reg_r15w   = triton::arch::Register(triton::arch::x86::ID_REG_R15W);
        triton::arch::x86::x86_reg_r15b   = triton::arch::Register(triton::arch::x86::ID_REG_R15B);

        triton::arch::x86::x86_reg_mm0    = triton::arch::Register(triton::arch::x86::ID_REG_MM0);
        triton::arch::x86::x86_reg_mm1    = triton::arch::Register(triton::arch::x86::ID_REG_MM1);
        triton::arch::x86::x86_reg_mm2    = triton::arch::Register(triton::arch::x86::ID_REG_MM2);
        triton::arch::x86::x86_reg_mm3    = triton::arch::Register(triton::arch::x86::ID_REG_MM3);
        triton::arch::x86::x86_reg_mm4    = triton::arch::Register(triton::arch::x86::ID_REG_MM4);
        triton::arch::x86::x86_reg_mm5    = triton::arch::Register(triton::arch::x86::ID_REG_MM5);
        triton::arch::x86::x86_reg_mm6    = triton::arch::Register(triton::arch::x86::ID_REG_MM6);
        triton::arch::x86::x86_reg_mm7    = triton::arch::Register(triton::arch::x86::ID_REG_MM7);

        triton::arch::x86::x86_reg_xmm0   = triton::arch::Register(triton::arch::x86::ID_REG_XMM0);
        triton::arch::x86::x86_reg_xmm1   = triton::arch::Register(triton::arch::x86::ID_REG_XMM1);
        triton::arch::x86::x86_reg_xmm2   = triton::arch::Register(triton::arch::x86::ID_REG_XMM2);
        triton::arch::x86::x86_reg_xmm3   = triton::arch::Register(triton::arch::x86::ID_REG_XMM3);
        triton::arch::x86::x86_reg_xmm4   = triton::arch::Register(triton::arch::x86::ID_REG_XMM4);
        triton::arch::x86::x86_reg_xmm5   = triton::arch::Register(triton::arch::x86::ID_REG_XMM5);
        triton::arch::x86::x86_reg_xmm6   = triton::arch::Register(triton::arch::x86::ID_REG_XMM6);
        triton::arch::x86::x86_reg_xmm7   = triton::arch::Register(triton::arch::x86::ID_REG_XMM7);
        triton::arch::x86::x86_reg_xmm8   = triton::arch::Register(triton::arch::x86::ID_REG_XMM8);
        triton::arch::x86::x86_reg_xmm9   = triton::arch::Register(triton::arch::x86::ID_REG_XMM9);
        triton::arch::x86::x86_reg_xmm10  = triton::arch::Register(triton::arch::x86::ID_REG_XMM10);
        triton::arch::x86::x86_reg_xmm11  = triton::arch::Register(triton::arch::x86::ID_REG_XMM11);
        triton::arch::x86::x86_reg_xmm12  = triton::arch::Register(triton::arch::x86::ID_REG_XMM12);
        triton::arch::x86::x86_reg_xmm13  = triton::arch::Register(triton::arch::x86::ID_REG_XMM13);
        triton::arch::x86::x86_reg_xmm14  = triton::arch::Register(triton::arch::x86::ID_REG_XMM14);
        triton::arch::x86::x86_reg_xmm15  = triton::arch::Register(triton::arch::x86::ID_REG_XMM15);

        triton::arch::x86::x86_reg_ymm0   = triton::arch::Register(triton::arch::x86::ID_REG_YMM0);
        triton::arch::x86::x86_reg_ymm1   = triton::arch::Register(triton::arch::x86::ID_REG_YMM1);
        triton::arch::x86::x86_reg_ymm2   = triton::arch::Register(triton::arch::x86::ID_REG_YMM2);
        triton::arch::x86::x86_reg_ymm3   = triton::arch::Register(triton::arch::x86::ID_REG_YMM3);
        triton::arch::x86::x86_reg_ymm4   = triton::arch::Register(triton::arch::x86::ID_REG_YMM4);
        triton::arch::x86::x86_reg_ymm5   = triton::arch::Register(triton::arch::x86::ID_REG_YMM5);
        triton::arch::x86::x86_reg_ymm6   = triton::arch::Register(triton::arch::x86::ID_REG_YMM6);
        triton::arch::x86::x86_reg_ymm7   = triton::arch::Register(triton::arch::x86::ID_REG_YMM7);
        triton::arch::x86::x86_reg_ymm8   = triton::arch::Register(triton::arch::x86::ID_REG_YMM8);
        triton::arch::x86::x86_reg_ymm9   = triton::arch::Register(triton::arch::x86::ID_REG_YMM9);
        triton::arch::x86::x86_reg_ymm10  = triton::arch::Register(triton::arch::x86::ID_REG_YMM10);
        triton::arch::x86::x86_reg_ymm11  = triton::arch::Register(triton::arch::x86::ID_REG_YMM11);
        triton::arch::x86::x86_reg_ymm12  = triton::arch::Register(triton::arch::x86::ID_REG_YMM12);
        triton::arch::x86::x86_reg_ymm13  = triton::arch::Register(triton::arch::x86::ID_REG_YMM13);
        triton::arch::x86::x86_reg_ymm14  = triton::arch::Register(triton::arch::x86::ID_REG_YMM14);
        triton::arch::x86::x86_reg_ymm15  = triton::arch::Register(triton::arch::x86::ID_REG_YMM15);

        triton::arch::x86::x86_reg_zmm0   = triton::arch::Register(triton::arch::x86::ID_REG_ZMM0);
        triton::arch::x86::x86_reg_zmm1   = triton::arch::Register(triton::arch::x86::ID_REG_ZMM1);
        triton::arch::x86::x86_reg_zmm2   = triton::arch::Register(triton::arch::x86::ID_REG_ZMM2);
        triton::arch::x86::x86_reg_zmm3   = triton::arch::Register(triton::arch::x86::ID_REG_ZMM3);
        triton::arch::x86::x86_reg_zmm4   = triton::arch::Register(triton::arch::x86::ID_REG_ZMM4);
        triton::arch::x86::x86_reg_zmm5   = triton::arch::Register(triton::arch::x86::ID_REG_ZMM5);
        triton::arch::x86::x86_reg_zmm6   = triton::arch::Register(triton::arch::x86::ID_REG_ZMM6);
        triton::arch::x86::x86_reg_zmm7   = triton::arch::Register(triton::arch::x86::ID_REG_ZMM7);
        triton::arch::x86::x86_reg_zmm8   = triton::arch::Register(triton::arch::x86::ID_REG_ZMM8);
        triton::arch::x86::x86_reg_zmm9   = triton::arch::Register(triton::arch::x86::ID_REG_ZMM9);
        triton::arch::x86::x86_reg_zmm10  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM10);
        triton::arch::x86::x86_reg_zmm11  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM11);
        triton::arch::x86::x86_reg_zmm12  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM12);
        triton::arch::x86::x86_reg_zmm13  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM13);
        triton::arch::x86::x86_reg_zmm14  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM14);
        triton::arch::x86::x86_reg_zmm15  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM15);
        triton::arch::x86::x86_reg_zmm16  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM16);
        triton::arch::x86::x86_reg_zmm17  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM17);
        triton::arch::x86::x86_reg_zmm18  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM18);
        triton::arch::x86::x86_reg_zmm19  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM19);
        triton::arch::x86::x86_reg_zmm20  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM20);
        triton::arch::x86::x86_reg_zmm21  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM21);
        triton::arch::x86::x86_reg_zmm22  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM22);
        triton::arch::x86::x86_reg_zmm23  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM23);
        triton::arch::x86::x86_reg_zmm24  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM24);
        triton::arch::x86::x86_reg_zmm25  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM25);
        triton::arch::x86::x86_reg_zmm26  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM26);
        triton::arch::x86::x86_reg_zmm27  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM27);
        triton::arch::x86::x86_reg_zmm28  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM28);
        triton::arch::x86::x86_reg_zmm29  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM29);
        triton::arch::x86::x86_reg_zmm30  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM30);
        triton::arch::x86::x86_reg_zmm31  = triton::arch::Register(triton::arch::x86::ID_REG_ZMM31);

        triton::arch::x86::x86_reg_mxcsr  = triton::arch::Register(triton::arch::x86::ID_REG_MXCSR);

        triton::arch::x86::x86_reg_cr0    = triton::arch::Register(triton::arch::x86::ID_REG_CR0);
        triton::arch::x86::x86_reg_cr1    = triton::arch::Register(triton::arch::x86::ID_REG_CR1);
        triton::arch::x86::x86_reg_cr2    = triton::arch::Register(triton::arch::x86::ID_REG_CR2);
        triton::arch::x86::x86_reg_cr3    = triton::arch::Register(triton::arch::x86::ID_REG_CR3);
        triton::arch::x86::x86_reg_cr4    = triton::arch::Register(triton::arch::x86::ID_REG_CR4);
        triton::arch::x86::x86_reg_cr5    = triton::arch::Register(triton::arch::x86::ID_REG_CR5);
        triton::arch::x86::x86_reg_cr6    = triton::arch::Register(triton::arch::x86::ID_REG_CR6);
        triton::arch::x86::x86_reg_cr7    = triton::arch::Register(triton::arch::x86::ID_REG_CR7);
        triton::arch::x86::x86_reg_cr8    = triton::arch::Register(triton::arch::x86::ID_REG_CR8);
        triton::arch::x86::x86_reg_cr9    = triton::arch::Register(triton::arch::x86::ID_REG_CR9);
        triton::arch::x86::x86_reg_cr10   = triton::arch::Register(triton::arch::x86::ID_REG_CR10);
        triton::arch::x86::x86_reg_cr11   = triton::arch::Register(triton::arch::x86::ID_REG_CR11);
        triton::arch::x86::x86_reg_cr12   = triton::arch::Register(triton::arch::x86::ID_REG_CR12);
        triton::arch::x86::x86_reg_cr13   = triton::arch::Register(triton::arch::x86::ID_REG_CR13);
        triton::arch::x86::x86_reg_cr14   = triton::arch::Register(triton::arch::x86::ID_REG_CR14);
        triton::arch::x86::x86_reg_cr15   = triton::arch::Register(triton::arch::x86::ID_REG_CR15);

        triton::arch::x86::x86_reg_ie     = triton::arch::Register(triton::arch::x86::ID_REG_IE);
        triton::arch::x86::x86_reg_de     = triton::arch::Register(triton::arch::x86::ID_REG_DE);
        triton::arch::x86::x86_reg_ze     = triton::arch::Register(triton::arch::x86::ID_REG_ZE);
        triton::arch::x86::x86_reg_oe     = triton::arch::Register(triton::arch::x86::ID_REG_OE);
        triton::arch::x86::x86_reg_ue     = triton::arch::Register(triton::arch::x86::ID_REG_UE);
        triton::arch::x86::x86_reg_pe     = triton::arch::Register(triton::arch::x86::ID_REG_PE);
        triton::arch::x86::x86_reg_daz    = triton::arch::Register(triton::arch::x86::ID_REG_DAZ);
        triton::arch::x86::x86_reg_im     = triton::arch::Register(triton::arch::x86::ID_REG_IM);
        triton::arch::x86::x86_reg_dm     = triton::arch::Register(triton::arch::x86::ID_REG_DM);
        triton::arch::x86::x86_reg_zm     = triton::arch::Register(triton::arch::x86::ID_REG_ZM);
        triton::arch::x86::x86_reg_om     = triton::arch::Register(triton::arch::x86::ID_REG_OM);
        triton::arch::x86::x86_reg_um     = triton::arch::Register(triton::arch::x86::ID_REG_UM);
        triton::arch::x86::x86_reg_pm     = triton::arch::Register(triton::arch::x86::ID_REG_PM);
        triton::arch::x86::x86_reg_rl     = triton::arch::Register(triton::arch::x86::ID_REG_RL);
        triton::arch::x86::x86_reg_rh     = triton::arch::Register(triton::arch::x86::ID_REG_RH);
        triton::arch::x86::x86_reg_fz     = triton::arch::Register(triton::arch::x86::ID_REG_FZ);

        triton::arch::x86::x86_reg_af     = triton::arch::Register(triton::arch::x86::ID_REG_AF);
        triton::arch::x86::x86_reg_cf     = triton::arch::Register(triton::arch::x86::ID_REG_CF);
        triton::arch::x86::x86_reg_df     = triton::arch::Register(triton::arch::x86::ID_REG_DF);
        triton::arch::x86::x86_reg_if     = triton::arch::Register(triton::arch::x86::ID_REG_IF);
        triton::arch::x86::x86_reg_of     = triton::arch::Register(triton::arch::x86::ID_REG_OF);
        triton::arch::x86::x86_reg_pf     = triton::arch::Register(triton::arch::x86::ID_REG_PF);
        triton::arch::x86::x86_reg_sf     = triton::arch::Register(triton::arch::x86::ID_REG_SF);
        triton::arch::x86::x86_reg_tf     = triton::arch::Register(triton::arch::x86::ID_REG_TF);
        triton::arch::x86::x86_reg_zf     = triton::arch::Register(triton::arch::x86::ID_REG_ZF);

        triton::arch::x86::x86_reg_cs     = triton::arch::Register(triton::arch::x86::ID_REG_CS);
        triton::arch::x86::x86_reg_ds     = triton::arch::Register(triton::arch::x86::ID_REG_DS);
        triton::arch::x86::x86_reg_es     = triton::arch::Register(triton::arch::x86::ID_REG_ES);
        triton::arch::x86::x86_reg_fs     = triton::arch::Register(triton::arch::x86::ID_REG_FS);
        triton::arch::x86::x86_reg_gs     = triton::arch::Register(triton::arch::x86::ID_REG_GS);
        triton::arch::x86::x86_reg_ss     = triton::arch::Register(triton::arch::x86::ID_REG_SS);

        /* Update python env ======================================================== */
        #ifdef TRITON_PYTHON_BINDINGS
          triton::bindings::python::initRegNamespace();
          triton::bindings::python::initCpuSizeNamespace();
          triton::bindings::python::initX86OpcodesNamespace();
          triton::bindings::python::initX86PrefixesNamespace();
          #if defined(__unix__) || defined(__APPLE__)
            triton::bindings::python::initSyscallNamespace();
          #endif
        #endif
      }


      void x8664Cpu::clear(void) {
        /* Clear memory */
        this->memory.clear();

        /* Clear registers */
        memset(this->rax,     0x00, sizeof(this->rax));
        memset(this->rbx,     0x00, sizeof(this->rbx));
        memset(this->rcx,     0x00, sizeof(this->rcx));
        memset(this->rdx,     0x00, sizeof(this->rdx));
        memset(this->rdi,     0x00, sizeof(this->rdi));
        memset(this->rsi,     0x00, sizeof(this->rsi));
        memset(this->rsp,     0x00, sizeof(this->rsp));
        memset(this->rbp,     0x00, sizeof(this->rbp));
        memset(this->rip,     0x00, sizeof(this->rip));
        memset(this->eflags,  0x00, sizeof(this->eflags));
        memset(this->r8,      0x00, sizeof(this->r8));
        memset(this->r9,      0x00, sizeof(this->r9));
        memset(this->r10,     0x00, sizeof(this->r10));
        memset(this->r11,     0x00, sizeof(this->r11));
        memset(this->r12,     0x00, sizeof(this->r12));
        memset(this->r13,     0x00, sizeof(this->r13));
        memset(this->r14,     0x00, sizeof(this->r14));
        memset(this->r15,     0x00, sizeof(this->r15));
        memset(this->mm0,     0x00, sizeof(this->mm0));
        memset(this->mm1,     0x00, sizeof(this->mm1));
        memset(this->mm2,     0x00, sizeof(this->mm2));
        memset(this->mm3,     0x00, sizeof(this->mm3));
        memset(this->mm4,     0x00, sizeof(this->mm4));
        memset(this->mm5,     0x00, sizeof(this->mm5));
        memset(this->mm6,     0x00, sizeof(this->mm6));
        memset(this->mm7,     0x00, sizeof(this->mm7));
        memset(this->xmm0,    0x00, sizeof(this->xmm0));
        memset(this->xmm1,    0x00, sizeof(this->xmm1));
        memset(this->xmm2,    0x00, sizeof(this->xmm2));
        memset(this->xmm3,    0x00, sizeof(this->xmm3));
        memset(this->xmm4,    0x00, sizeof(this->xmm4));
        memset(this->xmm5,    0x00, sizeof(this->xmm5));
        memset(this->xmm6,    0x00, sizeof(this->xmm6));
        memset(this->xmm7,    0x00, sizeof(this->xmm7));
        memset(this->xmm8,    0x00, sizeof(this->xmm8));
        memset(this->xmm9,    0x00, sizeof(this->xmm9));
        memset(this->xmm10,   0x00, sizeof(this->xmm10));
        memset(this->xmm11,   0x00, sizeof(this->xmm11));
        memset(this->xmm12,   0x00, sizeof(this->xmm12));
        memset(this->xmm13,   0x00, sizeof(this->xmm13));
        memset(this->xmm14,   0x00, sizeof(this->xmm14));
        memset(this->xmm15,   0x00, sizeof(this->xmm15));
        memset(this->ymm0,    0x00, sizeof(this->ymm0));
        memset(this->ymm1,    0x00, sizeof(this->ymm1));
        memset(this->ymm2,    0x00, sizeof(this->ymm2));
        memset(this->ymm3,    0x00, sizeof(this->ymm3));
        memset(this->ymm4,    0x00, sizeof(this->ymm4));
        memset(this->ymm5,    0x00, sizeof(this->ymm5));
        memset(this->ymm6,    0x00, sizeof(this->ymm6));
        memset(this->ymm7,    0x00, sizeof(this->ymm7));
        memset(this->ymm8,    0x00, sizeof(this->ymm8));
        memset(this->ymm9,    0x00, sizeof(this->ymm9));
        memset(this->ymm10,   0x00, sizeof(this->ymm10));
        memset(this->ymm11,   0x00, sizeof(this->ymm11));
        memset(this->ymm12,   0x00, sizeof(this->ymm12));
        memset(this->ymm13,   0x00, sizeof(this->ymm13));
        memset(this->ymm14,   0x00, sizeof(this->ymm14));
        memset(this->ymm15,   0x00, sizeof(this->ymm15));
        memset(this->zmm0,    0x00, sizeof(this->zmm0));
        memset(this->zmm1,    0x00, sizeof(this->zmm1));
        memset(this->zmm2,    0x00, sizeof(this->zmm2));
        memset(this->zmm3,    0x00, sizeof(this->zmm3));
        memset(this->zmm4,    0x00, sizeof(this->zmm4));
        memset(this->zmm5,    0x00, sizeof(this->zmm5));
        memset(this->zmm6,    0x00, sizeof(this->zmm6));
        memset(this->zmm7,    0x00, sizeof(this->zmm7));
        memset(this->zmm8,    0x00, sizeof(this->zmm8));
        memset(this->zmm9,    0x00, sizeof(this->zmm9));
        memset(this->zmm10,   0x00, sizeof(this->zmm10));
        memset(this->zmm11,   0x00, sizeof(this->zmm11));
        memset(this->zmm12,   0x00, sizeof(this->zmm12));
        memset(this->zmm13,   0x00, sizeof(this->zmm13));
        memset(this->zmm14,   0x00, sizeof(this->zmm14));
        memset(this->zmm15,   0x00, sizeof(this->zmm15));
        memset(this->zmm16,   0x00, sizeof(this->zmm16));
        memset(this->zmm17,   0x00, sizeof(this->zmm17));
        memset(this->zmm18,   0x00, sizeof(this->zmm18));
        memset(this->zmm19,   0x00, sizeof(this->zmm19));
        memset(this->zmm20,   0x00, sizeof(this->zmm20));
        memset(this->zmm21,   0x00, sizeof(this->zmm21));
        memset(this->zmm22,   0x00, sizeof(this->zmm22));
        memset(this->zmm23,   0x00, sizeof(this->zmm23));
        memset(this->zmm24,   0x00, sizeof(this->zmm24));
        memset(this->zmm25,   0x00, sizeof(this->zmm25));
        memset(this->zmm26,   0x00, sizeof(this->zmm26));
        memset(this->zmm27,   0x00, sizeof(this->zmm27));
        memset(this->zmm28,   0x00, sizeof(this->zmm28));
        memset(this->zmm29,   0x00, sizeof(this->zmm29));
        memset(this->zmm30,   0x00, sizeof(this->zmm30));
        memset(this->zmm31,   0x00, sizeof(this->zmm31));
        memset(this->mxcsr,   0x00, sizeof(this->mxcsr));
        memset(this->cr0,     0x00, sizeof(this->cr0));
        memset(this->cr1,     0x00, sizeof(this->cr1));
        memset(this->cr2,     0x00, sizeof(this->cr2));
        memset(this->cr3,     0x00, sizeof(this->cr3));
        memset(this->cr4,     0x00, sizeof(this->cr4));
        memset(this->cr5,     0x00, sizeof(this->cr5));
        memset(this->cr6,     0x00, sizeof(this->cr6));
        memset(this->cr7,     0x00, sizeof(this->cr7));
        memset(this->cr8,     0x00, sizeof(this->cr8));
        memset(this->cr9,     0x00, sizeof(this->cr9));
        memset(this->cr10,    0x00, sizeof(this->cr10));
        memset(this->cr11,    0x00, sizeof(this->cr11));
        memset(this->cr12,    0x00, sizeof(this->cr12));
        memset(this->cr13,    0x00, sizeof(this->cr13));
        memset(this->cr14,    0x00, sizeof(this->cr14));
        memset(this->cr15,    0x00, sizeof(this->cr15));
        memset(this->cs,      0x00, sizeof(this->cs));
        memset(this->ds,      0x00, sizeof(this->ds));
        memset(this->es,      0x00, sizeof(this->es));
        memset(this->fs,      0x00, sizeof(this->fs));
        memset(this->gs,      0x00, sizeof(this->gs));
        memset(this->ss,      0x00, sizeof(this->ss));
      }


      void x8664Cpu::operator=(const x8664Cpu& other) {
        this->copy(other);
      }


      bool x8664Cpu::isFlag(triton::uint32 regId) const {
        return ((regId >= triton::arch::x86::ID_REG_AF && regId <= triton::arch::x86::ID_REG_FZ) ? true : false);
      }


      bool x8664Cpu::isRegister(triton::uint32 regId) const {
        return (this->isGPR(regId) || this->isMMX(regId) || this->isSSE(regId) || this->isAVX256(regId) || this->isAVX512(regId) || this->isControl(regId) || this->isSegment(regId));
      }


      bool x8664Cpu::isRegisterValid(triton::uint32 regId) const {
        return (this->isFlag(regId) || this->isRegister(regId));
      }


      bool x8664Cpu::isGPR(triton::uint32 regId) const {
        return ((regId >= triton::arch::x86::ID_REG_RAX && regId <= triton::arch::x86::ID_REG_EFLAGS) ? true : false);
      }


      bool x8664Cpu::isMMX(triton::uint32 regId) const {
        return ((regId >= triton::arch::x86::ID_REG_MM0 && regId <= triton::arch::x86::ID_REG_MM7) ? true : false);
      }


      bool x8664Cpu::isSSE(triton::uint32 regId) const {
        return ((regId >= triton::arch::x86::ID_REG_MXCSR && regId <= triton::arch::x86::ID_REG_XMM15) ? true : false);
      }


      bool x8664Cpu::isAVX256(triton::uint32 regId) const {
        return ((regId >= triton::arch::x86::ID_REG_YMM0 && regId <= triton::arch::x86::ID_REG_YMM15) ? true : false);
      }


      bool x8664Cpu::isAVX512(triton::uint32 regId) const {
        return ((regId >= triton::arch::x86::ID_REG_ZMM0 && regId <= triton::arch::x86::ID_REG_ZMM31) ? true : false);
      }


      bool x8664Cpu::isControl(triton::uint32 regId) const {
        return ((regId >= triton::arch::x86::ID_REG_CR0 && regId <= triton::arch::x86::ID_REG_CR15) ? true : false);
      }


      bool x8664Cpu::isSegment(triton::uint32 regId) const {
        return ((regId >= triton::arch::x86::ID_REG_CS && regId <= triton::arch::x86::ID_REG_SS) ? true : false);
      }


      triton::uint32 x8664Cpu::invalidRegister(void) const {
        return triton::arch::x86::ID_REG_INVALID;
      }


      triton::uint32 x8664Cpu::numberOfRegisters(void) const {
        return triton::arch::x86::ID_REG_LAST_ITEM;
      }


      triton::uint32 x8664Cpu::registerSize(void) const {
        return QWORD_SIZE;
      }


      triton::uint32 x8664Cpu::registerBitSize(void) const {
        return QWORD_SIZE_BIT;
      }


      std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> x8664Cpu::getRegisterInformation(triton::uint32 reg) const {
        return triton::arch::x86::registerIdToRegisterInformation(reg);
      }


      std::set<triton::arch::Register*> x8664Cpu::getAllRegisters(void) const {
        std::set<triton::arch::Register*> ret;

        for (triton::uint32 index = 0; index < triton::arch::x86::ID_REG_LAST_ITEM; index++) {
          if (this->isRegisterValid(triton::arch::x86::x86_regs[index]->getId()))
            ret.insert(triton::arch::x86::x86_regs[index]);
        }

        return ret;
      }


      std::set<triton::arch::Register*> x8664Cpu::getParentRegisters(void) const {
        std::set<triton::arch::Register*> ret;

        for (triton::uint32 index = 0; index < triton::arch::x86::ID_REG_LAST_ITEM; index++) {
          /* Add GPR */
          if (triton::arch::x86::x86_regs[index]->getSize() == this->registerSize())
            ret.insert(triton::arch::x86::x86_regs[index]);

          /* Add Flags */
          else if (this->isFlag(triton::arch::x86::x86_regs[index]->getId()))
            ret.insert(triton::arch::x86::x86_regs[index]);

          /* Add MMX */
          else if (this->isMMX(triton::arch::x86::x86_regs[index]->getId()))
            ret.insert(triton::arch::x86::x86_regs[index]);

          /* Add SSE */
          else if (this->isSSE(triton::arch::x86::x86_regs[index]->getId()))
            ret.insert(triton::arch::x86::x86_regs[index]);

          /* Add AVX-256 */
          else if (this->isAVX256(triton::arch::x86::x86_regs[index]->getId()))
            ret.insert(triton::arch::x86::x86_regs[index]);

          /* Add AVX-512 */
          else if (this->isAVX512(triton::arch::x86::x86_regs[index]->getId()))
            ret.insert(triton::arch::x86::x86_regs[index]);

          /* Add Control */
          else if (this->isControl(triton::arch::x86::x86_regs[index]->getId()))
            ret.insert(triton::arch::x86::x86_regs[index]);
        }

        return ret;
      }


      void x8664Cpu::disassembly(triton::arch::Instruction& inst) const {
        triton::extlibs::capstone::csh       handle;
        triton::extlibs::capstone::cs_insn*  insn;
        triton::usize                        count = 0;

        /* Check if the opcodes and opcodes' size are defined */
        if (inst.getOpcodes() == nullptr || inst.getSize() == 0)
          throw triton::exceptions::Disassembly("x8664Cpu::disassembly(): Opcodes and opcodesSize must be definied.");

        /* Open capstone */
        if (triton::extlibs::capstone::cs_open(triton::extlibs::capstone::CS_ARCH_X86, triton::extlibs::capstone::CS_MODE_64, &handle) != triton::extlibs::capstone::CS_ERR_OK)
          throw triton::exceptions::Disassembly("x8664Cpu::disassembly(): Cannot open capstone.");

        /* Init capstone's options */
        triton::extlibs::capstone::cs_option(handle, triton::extlibs::capstone::CS_OPT_DETAIL, triton::extlibs::capstone::CS_OPT_ON);
        triton::extlibs::capstone::cs_option(handle, triton::extlibs::capstone::CS_OPT_SYNTAX, triton::extlibs::capstone::CS_OPT_SYNTAX_INTEL);

        /* Let's disass and build our operands */
        count = triton::extlibs::capstone::cs_disasm(handle, inst.getOpcodes(), inst.getSize(), inst.getAddress(), 0, &insn);
        if (count > 0) {
          triton::extlibs::capstone::cs_detail* detail = insn->detail;
          for (triton::uint32 j = 0; j < 1; j++) {

            /* Init the disassembly */
            std::stringstream str;
            str << insn[j].mnemonic << " " <<  insn[j].op_str;
            inst.setDisassembly(str.str());

            /* Refine the size */
            inst.setSize(insn[j].size);

            /* Init the instruction's type */
            inst.setType(triton::arch::x86::capstoneInstructionToTritonInstruction(insn[j].id));

            /* Init the instruction's prefix */
            inst.setPrefix(triton::arch::x86::capstonePrefixToTritonPrefix(detail->x86.prefix[0]));

            /* Init operands */
            for (triton::uint32 n = 0; n < detail->x86.op_count; n++) {
              triton::extlibs::capstone::cs_x86_op* op = &(detail->x86.operands[n]);
              switch(op->type) {

                case triton::extlibs::capstone::X86_OP_IMM:
                  inst.operands.push_back(triton::arch::OperandWrapper(triton::arch::Immediate(op->imm, op->size)));
                  break;

                case triton::extlibs::capstone::X86_OP_MEM: {
                  triton::arch::MemoryAccess mem = inst.popMemoryAccess();

                  /* Set the size if the memory is not valid */
                  if (!mem.isValid())
                    mem.setPair(std::make_pair(((op->size * BYTE_SIZE_BIT) - 1), 0));

                  /* LEA if exists */
                  triton::arch::Register segment(triton::arch::x86::capstoneRegisterToTritonRegister(op->mem.segment));
                  triton::arch::Register base(triton::arch::x86::capstoneRegisterToTritonRegister(op->mem.base));
                  triton::arch::Register index(triton::arch::x86::capstoneRegisterToTritonRegister(op->mem.index));
                  triton::arch::Immediate disp(op->mem.disp, base.isValid() ? base.getSize() : index.isValid() ? index.getSize() : op->size);
                  triton::arch::Immediate scale(op->mem.scale, base.isValid() ? base.getSize() : index.isValid() ? index.getSize() : op->size);

                  /* Specify that LEA contains a PC relative */
                  if (base.getId() == TRITON_X86_REG_PC.getId())
                    mem.setPcRelative(inst.getNextAddress());

                  mem.setSegmentRegister(segment);
                  mem.setBaseRegister(base);
                  mem.setIndexRegister(index);
                  mem.setDisplacement(disp);
                  mem.setScale(scale);

                  inst.operands.push_back(triton::arch::OperandWrapper(mem));
                  break;
                }

                case triton::extlibs::capstone::X86_OP_REG:
                  inst.operands.push_back(triton::arch::OperandWrapper(inst.getRegisterState(triton::arch::x86::capstoneRegisterToTritonRegister(op->reg))));
                  break;

                default:
                  throw triton::exceptions::Disassembly("x8664Cpu::disassembly(): Invalid operand.");
              }
            }

          }
          /* Set branch */
          if (detail->groups_count > 0) {
            for (triton::uint32 n = 0; n < detail->groups_count; n++) {
              if (detail->groups[n] == triton::extlibs::capstone::X86_GRP_JUMP)
                inst.setBranch(true);
              if (detail->groups[n] == triton::extlibs::capstone::X86_GRP_JUMP ||
                  detail->groups[n] == triton::extlibs::capstone::X86_GRP_CALL ||
                  detail->groups[n] == triton::extlibs::capstone::X86_GRP_RET)
                inst.setControlFlow(true);
            }
          }
          /* Free capstone stuffs */
          triton::extlibs::capstone::cs_free(insn, count);
        }
        else
          throw triton::exceptions::Disassembly("x8664Cpu::disassembly(): Failed to disassemble the given code.");

        triton::extlibs::capstone::cs_close(&handle);
        return;
      }


      void x8664Cpu::buildSemantics(triton::arch::Instruction& inst) const {
        if (!inst.getType())
          throw triton::exceptions::Cpu("x8664Cpu::buildSemantics(): You must disassemble the instruction before.");
        triton::arch::x86::semantics::build(inst);
      }


      triton::uint8 x8664Cpu::getConcreteMemoryValue(triton::uint64 addr) const {
        if (this->memory.find(addr) == this->memory.end())
          return 0x00;
        return this->memory.at(addr);
      }


      triton::uint512 x8664Cpu::getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks) const {
        triton::uint512 ret = 0;
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();

        if (size == 0 || size > DQQWORD_SIZE)
          throw triton::exceptions::Cpu("x8664Cpu::getConcreteMemoryValue(): Invalid size memory.");

        if (execCallbacks)
          triton::api.processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, mem);

        for (triton::sint32 i = size-1; i >= 0; i--)
          ret = ((ret << BYTE_SIZE_BIT) | this->getConcreteMemoryValue(addr+i));

        return ret;
      }


      std::vector<triton::uint8> x8664Cpu::getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks) const {
        std::vector<triton::uint8> area;

        for (triton::usize index = 0; index < size; index++) {
          if (execCallbacks)
            triton::api.processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, MemoryAccess(baseAddr+index, BYTE_SIZE));
          area.push_back(this->getConcreteMemoryValue(baseAddr+index));
        }

        return area;
      }


      triton::uint512 x8664Cpu::getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks) const {
        triton::uint512 value = 0;

        if (execCallbacks)
          triton::api.processCallbacks(triton::callbacks::GET_CONCRETE_REGISTER_VALUE, reg);

        switch (reg.getId()) {
          case triton::arch::x86::ID_REG_RAX: return (*((triton::uint64*)(this->rax)));
          case triton::arch::x86::ID_REG_EAX: return (*((triton::uint32*)(this->rax)));
          case triton::arch::x86::ID_REG_AX:  return (*((triton::uint16*)(this->rax)));
          case triton::arch::x86::ID_REG_AH:  return (*((triton::uint8*)(this->rax+1)));
          case triton::arch::x86::ID_REG_AL:  return (*((triton::uint8*)(this->rax)));

          case triton::arch::x86::ID_REG_RBX: return (*((triton::uint64*)(this->rbx)));
          case triton::arch::x86::ID_REG_EBX: return (*((triton::uint32*)(this->rbx)));
          case triton::arch::x86::ID_REG_BX:  return (*((triton::uint16*)(this->rbx)));
          case triton::arch::x86::ID_REG_BH:  return (*((triton::uint8*)(this->rbx+1)));
          case triton::arch::x86::ID_REG_BL:  return (*((triton::uint8*)(this->rbx)));

          case triton::arch::x86::ID_REG_RCX: return (*((triton::uint64*)(this->rcx)));
          case triton::arch::x86::ID_REG_ECX: return (*((triton::uint32*)(this->rcx)));
          case triton::arch::x86::ID_REG_CX:  return (*((triton::uint16*)(this->rcx)));
          case triton::arch::x86::ID_REG_CH:  return (*((triton::uint8*)(this->rcx+1)));
          case triton::arch::x86::ID_REG_CL:  return (*((triton::uint8*)(this->rcx)));

          case triton::arch::x86::ID_REG_RDX: return (*((triton::uint64*)(this->rdx)));
          case triton::arch::x86::ID_REG_EDX: return (*((triton::uint32*)(this->rdx)));
          case triton::arch::x86::ID_REG_DX:  return (*((triton::uint16*)(this->rdx)));
          case triton::arch::x86::ID_REG_DH:  return (*((triton::uint8*)(this->rdx+1)));
          case triton::arch::x86::ID_REG_DL:  return (*((triton::uint8*)(this->rdx)));

          case triton::arch::x86::ID_REG_RDI: return (*((triton::uint64*)(this->rdi)));
          case triton::arch::x86::ID_REG_EDI: return (*((triton::uint32*)(this->rdi)));
          case triton::arch::x86::ID_REG_DI:  return (*((triton::uint16*)(this->rdi)));
          case triton::arch::x86::ID_REG_DIL: return (*((triton::uint8*)(this->rdi)));

          case triton::arch::x86::ID_REG_RSI: return (*((triton::uint64*)(this->rsi)));
          case triton::arch::x86::ID_REG_ESI: return (*((triton::uint32*)(this->rsi)));
          case triton::arch::x86::ID_REG_SI:  return (*((triton::uint16*)(this->rsi)));
          case triton::arch::x86::ID_REG_SIL: return (*((triton::uint8*)(this->rsi)));

          case triton::arch::x86::ID_REG_RSP: return (*((triton::uint64*)(this->rsp)));
          case triton::arch::x86::ID_REG_ESP: return (*((triton::uint32*)(this->rsp)));
          case triton::arch::x86::ID_REG_SP:  return (*((triton::uint16*)(this->rsp)));
          case triton::arch::x86::ID_REG_SPL: return (*((triton::uint8*)(this->rsp)));

          case triton::arch::x86::ID_REG_RBP: return (*((triton::uint64*)(this->rbp)));
          case triton::arch::x86::ID_REG_EBP: return (*((triton::uint32*)(this->rbp)));
          case triton::arch::x86::ID_REG_BP:  return (*((triton::uint16*)(this->rbp)));
          case triton::arch::x86::ID_REG_BPL: return (*((triton::uint8*)(this->rbp)));

          case triton::arch::x86::ID_REG_RIP: return (*((triton::uint64*)(this->rip)));
          case triton::arch::x86::ID_REG_EIP: return (*((triton::uint32*)(this->rip)));
          case triton::arch::x86::ID_REG_IP:  return (*((triton::uint16*)(this->rip)));

          case triton::arch::x86::ID_REG_EFLAGS: return (*((triton::uint64*)(this->eflags)));

          case triton::arch::x86::ID_REG_R8:  return (*((triton::uint64*)(this->r8)));
          case triton::arch::x86::ID_REG_R8D: return (*((triton::uint32*)(this->r8)));
          case triton::arch::x86::ID_REG_R8W: return (*((triton::uint16*)(this->r8)));
          case triton::arch::x86::ID_REG_R8B: return (*((triton::uint8*)(this->r8)));

          case triton::arch::x86::ID_REG_R9:  return (*((triton::uint64*)(this->r9)));
          case triton::arch::x86::ID_REG_R9D: return (*((triton::uint32*)(this->r9)));
          case triton::arch::x86::ID_REG_R9W: return (*((triton::uint16*)(this->r9)));
          case triton::arch::x86::ID_REG_R9B: return (*((triton::uint8*)(this->r9)));

          case triton::arch::x86::ID_REG_R10:  return (*((triton::uint64*)(this->r10)));
          case triton::arch::x86::ID_REG_R10D: return (*((triton::uint32*)(this->r10)));
          case triton::arch::x86::ID_REG_R10W: return (*((triton::uint16*)(this->r10)));
          case triton::arch::x86::ID_REG_R10B: return (*((triton::uint8*)(this->r10)));

          case triton::arch::x86::ID_REG_R11:  return (*((triton::uint64*)(this->r11)));
          case triton::arch::x86::ID_REG_R11D: return (*((triton::uint32*)(this->r11)));
          case triton::arch::x86::ID_REG_R11W: return (*((triton::uint16*)(this->r11)));
          case triton::arch::x86::ID_REG_R11B: return (*((triton::uint8*)(this->r11)));

          case triton::arch::x86::ID_REG_R12:  return (*((triton::uint64*)(this->r12)));
          case triton::arch::x86::ID_REG_R12D: return (*((triton::uint32*)(this->r12)));
          case triton::arch::x86::ID_REG_R12W: return (*((triton::uint16*)(this->r12)));
          case triton::arch::x86::ID_REG_R12B: return (*((triton::uint8*)(this->r12)));

          case triton::arch::x86::ID_REG_R13:  return (*((triton::uint64*)(this->r13)));
          case triton::arch::x86::ID_REG_R13D: return (*((triton::uint32*)(this->r13)));
          case triton::arch::x86::ID_REG_R13W: return (*((triton::uint16*)(this->r13)));
          case triton::arch::x86::ID_REG_R13B: return (*((triton::uint8*)(this->r13)));

          case triton::arch::x86::ID_REG_R14:  return (*((triton::uint64*)(this->r14)));
          case triton::arch::x86::ID_REG_R14D: return (*((triton::uint32*)(this->r14)));
          case triton::arch::x86::ID_REG_R14W: return (*((triton::uint16*)(this->r14)));
          case triton::arch::x86::ID_REG_R14B: return (*((triton::uint8*)(this->r14)));

          case triton::arch::x86::ID_REG_R15:  return (*((triton::uint64*)(this->r15)));
          case triton::arch::x86::ID_REG_R15D: return (*((triton::uint32*)(this->r15)));
          case triton::arch::x86::ID_REG_R15W: return (*((triton::uint16*)(this->r15)));
          case triton::arch::x86::ID_REG_R15B: return (*((triton::uint8*)(this->r15)));

          case triton::arch::x86::ID_REG_MM0:  return (*((triton::uint64*)(this->mm0)));
          case triton::arch::x86::ID_REG_MM1:  return (*((triton::uint64*)(this->mm1)));
          case triton::arch::x86::ID_REG_MM2:  return (*((triton::uint64*)(this->mm2)));
          case triton::arch::x86::ID_REG_MM3:  return (*((triton::uint64*)(this->mm3)));
          case triton::arch::x86::ID_REG_MM4:  return (*((triton::uint64*)(this->mm4)));
          case triton::arch::x86::ID_REG_MM5:  return (*((triton::uint64*)(this->mm5)));
          case triton::arch::x86::ID_REG_MM6:  return (*((triton::uint64*)(this->mm6)));
          case triton::arch::x86::ID_REG_MM7:  return (*((triton::uint64*)(this->mm7)));

          case triton::arch::x86::ID_REG_XMM0:  value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm0);  return value;
          case triton::arch::x86::ID_REG_XMM1:  value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm1);  return value;
          case triton::arch::x86::ID_REG_XMM2:  value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm2);  return value;
          case triton::arch::x86::ID_REG_XMM3:  value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm3);  return value;
          case triton::arch::x86::ID_REG_XMM4:  value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm4);  return value;
          case triton::arch::x86::ID_REG_XMM5:  value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm5);  return value;
          case triton::arch::x86::ID_REG_XMM6:  value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm6);  return value;
          case triton::arch::x86::ID_REG_XMM7:  value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm7);  return value;
          case triton::arch::x86::ID_REG_XMM8:  value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm8);  return value;
          case triton::arch::x86::ID_REG_XMM9:  value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm9);  return value;
          case triton::arch::x86::ID_REG_XMM10: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm10); return value;
          case triton::arch::x86::ID_REG_XMM11: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm11); return value;
          case triton::arch::x86::ID_REG_XMM12: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm12); return value;
          case triton::arch::x86::ID_REG_XMM13: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm13); return value;
          case triton::arch::x86::ID_REG_XMM14: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm14); return value;
          case triton::arch::x86::ID_REG_XMM15: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm15); return value;

          case triton::arch::x86::ID_REG_YMM0:  value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm0);  return value;
          case triton::arch::x86::ID_REG_YMM1:  value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm1);  return value;
          case triton::arch::x86::ID_REG_YMM2:  value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm2);  return value;
          case triton::arch::x86::ID_REG_YMM3:  value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm3);  return value;
          case triton::arch::x86::ID_REG_YMM4:  value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm4);  return value;
          case triton::arch::x86::ID_REG_YMM5:  value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm5);  return value;
          case triton::arch::x86::ID_REG_YMM6:  value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm6);  return value;
          case triton::arch::x86::ID_REG_YMM7:  value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm7);  return value;
          case triton::arch::x86::ID_REG_YMM8:  value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm8);  return value;
          case triton::arch::x86::ID_REG_YMM9:  value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm9);  return value;
          case triton::arch::x86::ID_REG_YMM10: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm10); return value;
          case triton::arch::x86::ID_REG_YMM11: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm11); return value;
          case triton::arch::x86::ID_REG_YMM12: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm12); return value;
          case triton::arch::x86::ID_REG_YMM13: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm13); return value;
          case triton::arch::x86::ID_REG_YMM14: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm14); return value;
          case triton::arch::x86::ID_REG_YMM15: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm15); return value;

          case triton::arch::x86::ID_REG_ZMM0:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm0);  return value;
          case triton::arch::x86::ID_REG_ZMM1:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm1);  return value;
          case triton::arch::x86::ID_REG_ZMM2:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm2);  return value;
          case triton::arch::x86::ID_REG_ZMM3:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm3);  return value;
          case triton::arch::x86::ID_REG_ZMM4:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm4);  return value;
          case triton::arch::x86::ID_REG_ZMM5:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm5);  return value;
          case triton::arch::x86::ID_REG_ZMM6:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm6);  return value;
          case triton::arch::x86::ID_REG_ZMM7:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm7);  return value;
          case triton::arch::x86::ID_REG_ZMM8:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm8);  return value;
          case triton::arch::x86::ID_REG_ZMM9:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm9);  return value;
          case triton::arch::x86::ID_REG_ZMM10: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm10); return value;
          case triton::arch::x86::ID_REG_ZMM11: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm11); return value;
          case triton::arch::x86::ID_REG_ZMM12: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm12); return value;
          case triton::arch::x86::ID_REG_ZMM13: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm13); return value;
          case triton::arch::x86::ID_REG_ZMM14: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm14); return value;
          case triton::arch::x86::ID_REG_ZMM15: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm15); return value;
          case triton::arch::x86::ID_REG_ZMM16: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm16); return value;
          case triton::arch::x86::ID_REG_ZMM17: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm17); return value;
          case triton::arch::x86::ID_REG_ZMM18: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm18); return value;
          case triton::arch::x86::ID_REG_ZMM19: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm19); return value;
          case triton::arch::x86::ID_REG_ZMM20: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm20); return value;
          case triton::arch::x86::ID_REG_ZMM21: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm21); return value;
          case triton::arch::x86::ID_REG_ZMM22: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm22); return value;
          case triton::arch::x86::ID_REG_ZMM23: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm23); return value;
          case triton::arch::x86::ID_REG_ZMM24: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm24); return value;
          case triton::arch::x86::ID_REG_ZMM25: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm25); return value;
          case triton::arch::x86::ID_REG_ZMM26: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm26); return value;
          case triton::arch::x86::ID_REG_ZMM27: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm27); return value;
          case triton::arch::x86::ID_REG_ZMM28: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm28); return value;
          case triton::arch::x86::ID_REG_ZMM29: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm29); return value;
          case triton::arch::x86::ID_REG_ZMM30: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm30); return value;
          case triton::arch::x86::ID_REG_ZMM31: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm31); return value;

          case triton::arch::x86::ID_REG_MXCSR: return (*((triton::uint64*)(this->mxcsr)));

          case triton::arch::x86::ID_REG_CR0:  return (*((triton::uint64*)(this->cr0)));
          case triton::arch::x86::ID_REG_CR1:  return (*((triton::uint64*)(this->cr1)));
          case triton::arch::x86::ID_REG_CR2:  return (*((triton::uint64*)(this->cr2)));
          case triton::arch::x86::ID_REG_CR3:  return (*((triton::uint64*)(this->cr3)));
          case triton::arch::x86::ID_REG_CR4:  return (*((triton::uint64*)(this->cr4)));
          case triton::arch::x86::ID_REG_CR5:  return (*((triton::uint64*)(this->cr5)));
          case triton::arch::x86::ID_REG_CR6:  return (*((triton::uint64*)(this->cr6)));
          case triton::arch::x86::ID_REG_CR7:  return (*((triton::uint64*)(this->cr7)));
          case triton::arch::x86::ID_REG_CR8:  return (*((triton::uint64*)(this->cr8)));
          case triton::arch::x86::ID_REG_CR9:  return (*((triton::uint64*)(this->cr9)));
          case triton::arch::x86::ID_REG_CR10: return (*((triton::uint64*)(this->cr10)));
          case triton::arch::x86::ID_REG_CR11: return (*((triton::uint64*)(this->cr11)));
          case triton::arch::x86::ID_REG_CR12: return (*((triton::uint64*)(this->cr12)));
          case triton::arch::x86::ID_REG_CR13: return (*((triton::uint64*)(this->cr13)));
          case triton::arch::x86::ID_REG_CR14: return (*((triton::uint64*)(this->cr14)));
          case triton::arch::x86::ID_REG_CR15: return (*((triton::uint64*)(this->cr15)));

          case triton::arch::x86::ID_REG_IE:  return (((*((triton::uint64*)(this->mxcsr))) >> 0) & 1);
          case triton::arch::x86::ID_REG_DE:  return (((*((triton::uint64*)(this->mxcsr))) >> 1) & 1);
          case triton::arch::x86::ID_REG_ZE:  return (((*((triton::uint64*)(this->mxcsr))) >> 2) & 1);
          case triton::arch::x86::ID_REG_OE:  return (((*((triton::uint64*)(this->mxcsr))) >> 3) & 1);
          case triton::arch::x86::ID_REG_UE:  return (((*((triton::uint64*)(this->mxcsr))) >> 4) & 1);
          case triton::arch::x86::ID_REG_PE:  return (((*((triton::uint64*)(this->mxcsr))) >> 5) & 1);
          case triton::arch::x86::ID_REG_DAZ: return (((*((triton::uint64*)(this->mxcsr))) >> 6) & 1);
          case triton::arch::x86::ID_REG_IM:  return (((*((triton::uint64*)(this->mxcsr))) >> 7) & 1);
          case triton::arch::x86::ID_REG_DM:  return (((*((triton::uint64*)(this->mxcsr))) >> 8) & 1);
          case triton::arch::x86::ID_REG_ZM:  return (((*((triton::uint64*)(this->mxcsr))) >> 9) & 1);
          case triton::arch::x86::ID_REG_OM:  return (((*((triton::uint64*)(this->mxcsr))) >> 10) & 1);
          case triton::arch::x86::ID_REG_UM:  return (((*((triton::uint64*)(this->mxcsr))) >> 11) & 1);
          case triton::arch::x86::ID_REG_PM:  return (((*((triton::uint64*)(this->mxcsr))) >> 12) & 1);
          case triton::arch::x86::ID_REG_RL:  return (((*((triton::uint64*)(this->mxcsr))) >> 13) & 1);
          case triton::arch::x86::ID_REG_RH:  return (((*((triton::uint64*)(this->mxcsr))) >> 14) & 1);
          case triton::arch::x86::ID_REG_FZ:  return (((*((triton::uint64*)(this->mxcsr))) >> 15) & 1);

          case triton::arch::x86::ID_REG_CF: return (((*((triton::uint64*)(this->eflags))) >> 0) & 1);
          case triton::arch::x86::ID_REG_PF: return (((*((triton::uint64*)(this->eflags))) >> 2) & 1);
          case triton::arch::x86::ID_REG_AF: return (((*((triton::uint64*)(this->eflags))) >> 4) & 1);
          case triton::arch::x86::ID_REG_ZF: return (((*((triton::uint64*)(this->eflags))) >> 6) & 1);
          case triton::arch::x86::ID_REG_SF: return (((*((triton::uint64*)(this->eflags))) >> 7) & 1);
          case triton::arch::x86::ID_REG_TF: return (((*((triton::uint64*)(this->eflags))) >> 8) & 1);
          case triton::arch::x86::ID_REG_IF: return (((*((triton::uint64*)(this->eflags))) >> 9) & 1);
          case triton::arch::x86::ID_REG_DF: return (((*((triton::uint64*)(this->eflags))) >> 10) & 1);
          case triton::arch::x86::ID_REG_OF: return (((*((triton::uint64*)(this->eflags))) >> 11) & 1);

          case triton::arch::x86::ID_REG_CS: return (*((triton::uint64*)(this->cs)));
          case triton::arch::x86::ID_REG_DS: return (*((triton::uint64*)(this->ds)));
          case triton::arch::x86::ID_REG_ES: return (*((triton::uint64*)(this->es)));
          case triton::arch::x86::ID_REG_FS: return (*((triton::uint64*)(this->fs)));
          case triton::arch::x86::ID_REG_GS: return (*((triton::uint64*)(this->gs)));
          case triton::arch::x86::ID_REG_SS: return (*((triton::uint64*)(this->ss)));

          default:
            throw triton::exceptions::Cpu("x8664Cpu::getConcreteRegisterValue(): Invalid register.");
        }

        return value;
      }


      void x8664Cpu::setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value) {
        this->memory[addr] = value;
      }


      void x8664Cpu::setConcreteMemoryValue(const triton::arch::MemoryAccess& mem) {
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();
        triton::uint512 cv  = mem.getConcreteValue();

        if (size == 0 || size > DQQWORD_SIZE)
          throw triton::exceptions::Cpu("x8664Cpu::setConcreteMemoryValue(): Invalid size memory.");

        for (triton::uint32 i = 0; i < size; i++) {
          this->memory[addr+i] = (cv & 0xff).convert_to<triton::uint8>();
          cv >>= 8;
        }
      }


      void x8664Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values) {
        for (triton::usize index = 0; index < values.size(); index++) {
          this->memory[baseAddr+index] = values[index];
        }
      }


      void x8664Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          this->memory[baseAddr+index] = area[index];
        }
      }


      void x8664Cpu::setConcreteRegisterValue(const triton::arch::Register& reg) {
        triton::uint512 value = reg.getConcreteValue();

        switch (reg.getId()) {
          case triton::arch::x86::ID_REG_RAX: (*((triton::uint64*)(this->rax)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_EAX: (*((triton::uint32*)(this->rax)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_AX:  (*((triton::uint16*)(this->rax)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::x86::ID_REG_AH:  (*((triton::uint8*)(this->rax+1))) = value.convert_to<triton::uint8>(); break;
          case triton::arch::x86::ID_REG_AL:  (*((triton::uint8*)(this->rax)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::x86::ID_REG_RBX: (*((triton::uint64*)(this->rbx)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_EBX: (*((triton::uint32*)(this->rbx)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_BX:  (*((triton::uint16*)(this->rbx)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::x86::ID_REG_BH:  (*((triton::uint8*)(this->rbx+1))) = value.convert_to<triton::uint8>(); break;
          case triton::arch::x86::ID_REG_BL:  (*((triton::uint8*)(this->rbx)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::x86::ID_REG_RCX: (*((triton::uint64*)(this->rcx)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_ECX: (*((triton::uint32*)(this->rcx)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_CX:  (*((triton::uint16*)(this->rcx)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::x86::ID_REG_CH:  (*((triton::uint8*)(this->rcx+1))) = value.convert_to<triton::uint8>(); break;
          case triton::arch::x86::ID_REG_CL:  (*((triton::uint8*)(this->rcx)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::x86::ID_REG_RDX: (*((triton::uint64*)(this->rdx)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_EDX: (*((triton::uint32*)(this->rdx)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_DX:  (*((triton::uint16*)(this->rdx)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::x86::ID_REG_DH:  (*((triton::uint8*)(this->rdx+1))) = value.convert_to<triton::uint8>(); break;
          case triton::arch::x86::ID_REG_DL:  (*((triton::uint8*)(this->rdx)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::x86::ID_REG_RDI: (*((triton::uint64*)(this->rdi)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_EDI: (*((triton::uint32*)(this->rdi)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_DI:  (*((triton::uint16*)(this->rdi)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::x86::ID_REG_DIL: (*((triton::uint8*)(this->rdi)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::x86::ID_REG_RSI: (*((triton::uint64*)(this->rsi))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_ESI: (*((triton::uint32*)(this->rsi))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_SI:  (*((triton::uint16*)(this->rsi))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::x86::ID_REG_SIL: (*((triton::uint8*)(this->rsi)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::x86::ID_REG_RSP: (*((triton::uint64*)(this->rsp))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_ESP: (*((triton::uint32*)(this->rsp))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_SP:  (*((triton::uint16*)(this->rsp))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::x86::ID_REG_SPL: (*((triton::uint8*)(this->rsp)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::x86::ID_REG_RBP: (*((triton::uint64*)(this->rbp))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_EBP: (*((triton::uint32*)(this->rbp))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_BP:  (*((triton::uint16*)(this->rbp))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::x86::ID_REG_BPL: (*((triton::uint8*)(this->rbp)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::x86::ID_REG_RIP: (*((triton::uint64*)(this->rip))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_EIP: (*((triton::uint32*)(this->rip))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_IP:  (*((triton::uint16*)(this->rip))) = value.convert_to<triton::uint16>(); break;

          case triton::arch::x86::ID_REG_EFLAGS: (*((triton::uint64*)(this->eflags))) = value.convert_to<triton::uint64>(); break;

          case triton::arch::x86::ID_REG_CF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = value.convert_to<bool>() ? b | (1 << 0) : b & ~(1 << 0);
            break;
          }
          case triton::arch::x86::ID_REG_PF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = value.convert_to<bool>() ? b | (1 << 2) : b & ~(1 << 2);
            break;
          }
          case triton::arch::x86::ID_REG_AF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = value.convert_to<bool>() ? b | (1 << 4) : b & ~(1 << 4);
            break;
          }
          case triton::arch::x86::ID_REG_ZF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = value.convert_to<bool>() ? b | (1 << 6) : b & ~(1 << 6);
            break;
          }
          case triton::arch::x86::ID_REG_SF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = value.convert_to<bool>() ? b | (1 << 7) : b & ~(1 << 7);
            break;
          }
          case triton::arch::x86::ID_REG_TF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = value.convert_to<bool>() ? b | (1 << 8) : b & ~(1 << 8);
            break;
          }
          case triton::arch::x86::ID_REG_IF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = value.convert_to<bool>() ? b | (1 << 9) : b & ~(1 << 9);
            break;
          }
          case triton::arch::x86::ID_REG_DF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = value.convert_to<bool>() ? b | (1 << 10) : b & ~(1 << 10);
            break;
          }
          case triton::arch::x86::ID_REG_OF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = value.convert_to<bool>() ? b | (1 << 11) : b & ~(1 << 11);
            break;
          }

          case triton::arch::x86::ID_REG_R8:  (*((triton::uint64*)(this->r8))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_R8D: (*((triton::uint32*)(this->r8))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_R8W: (*((triton::uint16*)(this->r8))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::x86::ID_REG_R8B: (*((triton::uint8*)(this->r8)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::x86::ID_REG_R9:  (*((triton::uint64*)(this->r9))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_R9D: (*((triton::uint32*)(this->r9))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_R9W: (*((triton::uint16*)(this->r9))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::x86::ID_REG_R9B: (*((triton::uint8*)(this->r9)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::x86::ID_REG_R10:  (*((triton::uint64*)(this->r10))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_R10D: (*((triton::uint32*)(this->r10))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_R10W: (*((triton::uint16*)(this->r10))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::x86::ID_REG_R10B: (*((triton::uint8*)(this->r10)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::x86::ID_REG_R11:  (*((triton::uint64*)(this->r11))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_R11D: (*((triton::uint32*)(this->r11))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_R11W: (*((triton::uint16*)(this->r11))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::x86::ID_REG_R11B: (*((triton::uint8*)(this->r11)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::x86::ID_REG_R12:  (*((triton::uint64*)(this->r12))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_R12D: (*((triton::uint32*)(this->r12))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_R12W: (*((triton::uint16*)(this->r12))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::x86::ID_REG_R12B: (*((triton::uint8*)(this->r12)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::x86::ID_REG_R13:  (*((triton::uint64*)(this->r13))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_R13D: (*((triton::uint32*)(this->r13))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_R13W: (*((triton::uint16*)(this->r13))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::x86::ID_REG_R13B: (*((triton::uint8*)(this->r13)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::x86::ID_REG_R14:  (*((triton::uint64*)(this->r14))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_R14D: (*((triton::uint32*)(this->r14))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_R14W: (*((triton::uint16*)(this->r14))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::x86::ID_REG_R14B: (*((triton::uint8*)(this->r14)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::x86::ID_REG_R15:  (*((triton::uint64*)(this->r15))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_R15D: (*((triton::uint32*)(this->r15))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::x86::ID_REG_R15W: (*((triton::uint16*)(this->r15))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::x86::ID_REG_R15B: (*((triton::uint8*)(this->r15)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::x86::ID_REG_MM0:  (*((triton::uint64*)(this->mm0))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_MM1:  (*((triton::uint64*)(this->mm1))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_MM2:  (*((triton::uint64*)(this->mm2))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_MM3:  (*((triton::uint64*)(this->mm3))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_MM4:  (*((triton::uint64*)(this->mm4))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_MM5:  (*((triton::uint64*)(this->mm5))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_MM6:  (*((triton::uint64*)(this->mm6))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_MM7:  (*((triton::uint64*)(this->mm7))) = value.convert_to<triton::uint64>(); break;

          case triton::arch::x86::ID_REG_XMM0:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm0); break;
          case triton::arch::x86::ID_REG_XMM1:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm1); break;
          case triton::arch::x86::ID_REG_XMM2:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm2); break;
          case triton::arch::x86::ID_REG_XMM3:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm3); break;
          case triton::arch::x86::ID_REG_XMM4:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm4); break;
          case triton::arch::x86::ID_REG_XMM5:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm5); break;
          case triton::arch::x86::ID_REG_XMM6:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm6); break;
          case triton::arch::x86::ID_REG_XMM7:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm7); break;
          case triton::arch::x86::ID_REG_XMM8:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm8); break;
          case triton::arch::x86::ID_REG_XMM9:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm9); break;
          case triton::arch::x86::ID_REG_XMM10: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm10); break;
          case triton::arch::x86::ID_REG_XMM11: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm11); break;
          case triton::arch::x86::ID_REG_XMM12: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm12); break;
          case triton::arch::x86::ID_REG_XMM13: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm13); break;
          case triton::arch::x86::ID_REG_XMM14: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm14); break;
          case triton::arch::x86::ID_REG_XMM15: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm15); break;

          case triton::arch::x86::ID_REG_YMM0:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm0); break;
          case triton::arch::x86::ID_REG_YMM1:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm1); break;
          case triton::arch::x86::ID_REG_YMM2:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm2); break;
          case triton::arch::x86::ID_REG_YMM3:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm3); break;
          case triton::arch::x86::ID_REG_YMM4:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm4); break;
          case triton::arch::x86::ID_REG_YMM5:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm5); break;
          case triton::arch::x86::ID_REG_YMM6:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm6); break;
          case triton::arch::x86::ID_REG_YMM7:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm7); break;
          case triton::arch::x86::ID_REG_YMM8:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm8); break;
          case triton::arch::x86::ID_REG_YMM9:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm9); break;
          case triton::arch::x86::ID_REG_YMM10: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm10); break;
          case triton::arch::x86::ID_REG_YMM11: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm11); break;
          case triton::arch::x86::ID_REG_YMM12: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm12); break;
          case triton::arch::x86::ID_REG_YMM13: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm13); break;
          case triton::arch::x86::ID_REG_YMM14: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm14); break;
          case triton::arch::x86::ID_REG_YMM15: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm15); break;

          case triton::arch::x86::ID_REG_ZMM0:  triton::utils::fromUintToBuffer(value, this->zmm0); break;
          case triton::arch::x86::ID_REG_ZMM1:  triton::utils::fromUintToBuffer(value, this->zmm1); break;
          case triton::arch::x86::ID_REG_ZMM2:  triton::utils::fromUintToBuffer(value, this->zmm2); break;
          case triton::arch::x86::ID_REG_ZMM3:  triton::utils::fromUintToBuffer(value, this->zmm3); break;
          case triton::arch::x86::ID_REG_ZMM4:  triton::utils::fromUintToBuffer(value, this->zmm4); break;
          case triton::arch::x86::ID_REG_ZMM5:  triton::utils::fromUintToBuffer(value, this->zmm5); break;
          case triton::arch::x86::ID_REG_ZMM6:  triton::utils::fromUintToBuffer(value, this->zmm6); break;
          case triton::arch::x86::ID_REG_ZMM7:  triton::utils::fromUintToBuffer(value, this->zmm7); break;
          case triton::arch::x86::ID_REG_ZMM8:  triton::utils::fromUintToBuffer(value, this->zmm8); break;
          case triton::arch::x86::ID_REG_ZMM9:  triton::utils::fromUintToBuffer(value, this->zmm9); break;
          case triton::arch::x86::ID_REG_ZMM10: triton::utils::fromUintToBuffer(value, this->zmm10); break;
          case triton::arch::x86::ID_REG_ZMM11: triton::utils::fromUintToBuffer(value, this->zmm11); break;
          case triton::arch::x86::ID_REG_ZMM12: triton::utils::fromUintToBuffer(value, this->zmm12); break;
          case triton::arch::x86::ID_REG_ZMM13: triton::utils::fromUintToBuffer(value, this->zmm13); break;
          case triton::arch::x86::ID_REG_ZMM14: triton::utils::fromUintToBuffer(value, this->zmm14); break;
          case triton::arch::x86::ID_REG_ZMM15: triton::utils::fromUintToBuffer(value, this->zmm15); break;
          case triton::arch::x86::ID_REG_ZMM16: triton::utils::fromUintToBuffer(value, this->zmm16); break;
          case triton::arch::x86::ID_REG_ZMM17: triton::utils::fromUintToBuffer(value, this->zmm17); break;
          case triton::arch::x86::ID_REG_ZMM18: triton::utils::fromUintToBuffer(value, this->zmm18); break;
          case triton::arch::x86::ID_REG_ZMM19: triton::utils::fromUintToBuffer(value, this->zmm19); break;
          case triton::arch::x86::ID_REG_ZMM20: triton::utils::fromUintToBuffer(value, this->zmm20); break;
          case triton::arch::x86::ID_REG_ZMM21: triton::utils::fromUintToBuffer(value, this->zmm21); break;
          case triton::arch::x86::ID_REG_ZMM22: triton::utils::fromUintToBuffer(value, this->zmm22); break;
          case triton::arch::x86::ID_REG_ZMM23: triton::utils::fromUintToBuffer(value, this->zmm23); break;
          case triton::arch::x86::ID_REG_ZMM24: triton::utils::fromUintToBuffer(value, this->zmm24); break;
          case triton::arch::x86::ID_REG_ZMM25: triton::utils::fromUintToBuffer(value, this->zmm25); break;
          case triton::arch::x86::ID_REG_ZMM26: triton::utils::fromUintToBuffer(value, this->zmm26); break;
          case triton::arch::x86::ID_REG_ZMM27: triton::utils::fromUintToBuffer(value, this->zmm27); break;
          case triton::arch::x86::ID_REG_ZMM28: triton::utils::fromUintToBuffer(value, this->zmm28); break;
          case triton::arch::x86::ID_REG_ZMM29: triton::utils::fromUintToBuffer(value, this->zmm29); break;
          case triton::arch::x86::ID_REG_ZMM30: triton::utils::fromUintToBuffer(value, this->zmm30); break;
          case triton::arch::x86::ID_REG_ZMM31: triton::utils::fromUintToBuffer(value, this->zmm31); break;

          case triton::arch::x86::ID_REG_MXCSR: (*((triton::uint64*)(this->mxcsr))) = value.convert_to<triton::uint64>(); break;

          case triton::arch::x86::ID_REG_IE: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = value.convert_to<bool>() ? b | (1 << 0) : b & ~(1 << 0);
            break;
          }
          case triton::arch::x86::ID_REG_DE: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = value.convert_to<bool>() ? b | (1 << 1) : b & ~(1 << 1);
            break;
          }
          case triton::arch::x86::ID_REG_ZE: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = value.convert_to<bool>() ? b | (1 << 2) : b & ~(1 << 2);
            break;
          }
          case triton::arch::x86::ID_REG_OE: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = value.convert_to<bool>() ? b | (1 << 3) : b & ~(1 << 3);
            break;
          }
          case triton::arch::x86::ID_REG_UE: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = value.convert_to<bool>() ? b | (1 << 4) : b & ~(1 << 4);
            break;
          }
          case triton::arch::x86::ID_REG_PE: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = value.convert_to<bool>() ? b | (1 << 5) : b & ~(1 << 5);
            break;
          }
          case triton::arch::x86::ID_REG_DAZ: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = value.convert_to<bool>() ? b | (1 << 6) : b & ~(1 << 6);
            break;
          }
          case triton::arch::x86::ID_REG_IM: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = value.convert_to<bool>() ? b | (1 << 7) : b & ~(1 << 7);
            break;
          }
          case triton::arch::x86::ID_REG_DM: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = value.convert_to<bool>() ? b | (1 << 8) : b & ~(1 << 8);
            break;
          }
          case triton::arch::x86::ID_REG_ZM: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = value.convert_to<bool>() ? b | (1 << 9) : b & ~(1 << 9);
            break;
          }
          case triton::arch::x86::ID_REG_OM: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = value.convert_to<bool>() ? b | (1 << 10) : b & ~(1 << 10);
            break;
          }
          case triton::arch::x86::ID_REG_UM: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = value.convert_to<bool>() ? b | (1 << 11) : b & ~(1 << 11);
            break;
          }
          case triton::arch::x86::ID_REG_PM: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = value.convert_to<bool>() ? b | (1 << 12) : b & ~(1 << 12);
            break;
          }
          case triton::arch::x86::ID_REG_RL: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = value.convert_to<bool>() ? b | (1 << 13) : b & ~(1 << 13);
            break;
          }
          case triton::arch::x86::ID_REG_RH: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = value.convert_to<bool>() ? b | (1 << 14) : b & ~(1 << 14);
            break;
          }
          case triton::arch::x86::ID_REG_FZ: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = value.convert_to<bool>() ? b | (1 << 15) : b & ~(1 << 15);
            break;
          }

          case triton::arch::x86::ID_REG_CR0:  (*((triton::uint64*)(this->cr0)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_CR1:  (*((triton::uint64*)(this->cr1)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_CR2:  (*((triton::uint64*)(this->cr2)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_CR3:  (*((triton::uint64*)(this->cr3)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_CR4:  (*((triton::uint64*)(this->cr4)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_CR5:  (*((triton::uint64*)(this->cr5)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_CR6:  (*((triton::uint64*)(this->cr6)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_CR7:  (*((triton::uint64*)(this->cr7)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_CR8:  (*((triton::uint64*)(this->cr8)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_CR9:  (*((triton::uint64*)(this->cr9)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_CR10: (*((triton::uint64*)(this->cr10))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_CR11: (*((triton::uint64*)(this->cr11))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_CR12: (*((triton::uint64*)(this->cr12))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_CR13: (*((triton::uint64*)(this->cr13))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_CR14: (*((triton::uint64*)(this->cr14))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_CR15: (*((triton::uint64*)(this->cr15))) = value.convert_to<triton::uint64>(); break;

          case triton::arch::x86::ID_REG_CS:  (*((triton::uint64*)(this->cs))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_DS:  (*((triton::uint64*)(this->ds))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_ES:  (*((triton::uint64*)(this->es))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_FS:  (*((triton::uint64*)(this->fs))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_GS:  (*((triton::uint64*)(this->gs))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::x86::ID_REG_SS:  (*((triton::uint64*)(this->ss))) = value.convert_to<triton::uint64>(); break;

          default:
            throw triton::exceptions::Cpu("x8664Cpu:setConcreteRegisterValue(): Invalid register.");
        }
      }


      bool x8664Cpu::isMemoryMapped(triton::uint64 baseAddr, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) == this->memory.end())
            return false;
        }
        return true;
      }


      void x8664Cpu::unmapMemory(triton::uint64 baseAddr, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) != this->memory.end())
            this->memory.erase(baseAddr + index);
        }
      }

    }; /* x86 namespace */
  }; /* arch namespace */
}; /* triton namespace */

