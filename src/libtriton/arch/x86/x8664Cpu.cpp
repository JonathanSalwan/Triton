//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <architecture.hpp>
#include <coreUtils.hpp>
#include <cpuSize.hpp>
#include <immediateOperand.hpp>
#include <x8664Cpu.hpp>
#include <x86Specifications.hpp>

#ifdef __unix__
  #include <capstone/capstone.h>
#elif _WIN32
  #include <capstone.h>
#endif

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
    }


    void x8664Cpu::copy(const x8664Cpu& other) {
      this->memory = other.memory;
      (*((triton::uint64*)(this->rax)))    = (*((triton::uint64*)(other.rax)));
      (*((triton::uint64*)(this->rbx)))    = (*((triton::uint64*)(other.rbx)));
      (*((triton::uint64*)(this->rcx)))    = (*((triton::uint64*)(other.rcx)));
      (*((triton::uint64*)(this->rdx)))    = (*((triton::uint64*)(other.rdx)));
      (*((triton::uint64*)(this->rdi)))    = (*((triton::uint64*)(other.rdi)));
      (*((triton::uint64*)(this->rsi)))    = (*((triton::uint64*)(other.rsi)));
      (*((triton::uint64*)(this->rsp)))    = (*((triton::uint64*)(other.rsp)));
      (*((triton::uint64*)(this->rbp)))    = (*((triton::uint64*)(other.rbp)));
      (*((triton::uint64*)(this->rip)))    = (*((triton::uint64*)(other.rip)));
      (*((triton::uint64*)(this->rflags))) = (*((triton::uint64*)(other.rflags)));
      (*((triton::uint64*)(this->r8)))     = (*((triton::uint64*)(other.r8)));
      (*((triton::uint64*)(this->r9)))     = (*((triton::uint64*)(other.r9)));
      (*((triton::uint64*)(this->r10)))    = (*((triton::uint64*)(other.r10)));
      (*((triton::uint64*)(this->r11)))    = (*((triton::uint64*)(other.r11)));
      (*((triton::uint64*)(this->r12)))    = (*((triton::uint64*)(other.r12)));
      (*((triton::uint64*)(this->r13)))    = (*((triton::uint64*)(other.r13)));
      (*((triton::uint64*)(this->r14)))    = (*((triton::uint64*)(other.r14)));
      (*((triton::uint64*)(this->r15)))    = (*((triton::uint64*)(other.r15)));
      memcpy(this->xmm0, other.xmm0, sizeof(this->xmm0));
      memcpy(this->xmm1, other.xmm1, sizeof(this->xmm1));
      memcpy(this->xmm2, other.xmm2, sizeof(this->xmm2));
      memcpy(this->xmm3, other.xmm3, sizeof(this->xmm3));
      memcpy(this->xmm4, other.xmm4, sizeof(this->xmm4));
      memcpy(this->xmm5, other.xmm5, sizeof(this->xmm5));
      memcpy(this->xmm6, other.xmm6, sizeof(this->xmm6));
      memcpy(this->xmm7, other.xmm7, sizeof(this->xmm7));
      memcpy(this->xmm8, other.xmm8, sizeof(this->xmm8));
      memcpy(this->xmm9, other.xmm9, sizeof(this->xmm9));
      memcpy(this->xmm10, other.xmm10, sizeof(this->xmm10));
      memcpy(this->xmm11, other.xmm11, sizeof(this->xmm11));
      memcpy(this->xmm12, other.xmm12, sizeof(this->xmm12));
      memcpy(this->xmm13, other.xmm13, sizeof(this->xmm13));
      memcpy(this->xmm14, other.xmm14, sizeof(this->xmm14));
      memcpy(this->xmm15, other.xmm15, sizeof(this->xmm15));
    }


    void x8664Cpu::init(void) {
      /* Define registers ========================================================= */
      triton::arch::x86::x86_reg_rax    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RAX);
      triton::arch::x86::x86_reg_eax    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EAX);
      triton::arch::x86::x86_reg_ax     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_AX);
      triton::arch::x86::x86_reg_ah     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_AH);
      triton::arch::x86::x86_reg_al     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_AL);

      triton::arch::x86::x86_reg_rbx    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RBX);
      triton::arch::x86::x86_reg_ebx    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EBX);
      triton::arch::x86::x86_reg_bx     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_BX);
      triton::arch::x86::x86_reg_bh     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_BH);
      triton::arch::x86::x86_reg_bl     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_BL);

      triton::arch::x86::x86_reg_rcx    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RCX);
      triton::arch::x86::x86_reg_ecx    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_ECX);
      triton::arch::x86::x86_reg_cx     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_CX);
      triton::arch::x86::x86_reg_ch     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_CH);
      triton::arch::x86::x86_reg_cl     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_CL);

      triton::arch::x86::x86_reg_rdx    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RDX);
      triton::arch::x86::x86_reg_edx    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EDX);
      triton::arch::x86::x86_reg_dx     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_DX);
      triton::arch::x86::x86_reg_dh     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_DH);
      triton::arch::x86::x86_reg_dl     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_DL);

      triton::arch::x86::x86_reg_rdi    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RDI);
      triton::arch::x86::x86_reg_edi    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EDI);
      triton::arch::x86::x86_reg_di     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_DI);
      triton::arch::x86::x86_reg_dil    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_DIL);

      triton::arch::x86::x86_reg_rsi    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RSI);
      triton::arch::x86::x86_reg_esi    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_ESI);
      triton::arch::x86::x86_reg_si     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_SI);
      triton::arch::x86::x86_reg_sil    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_SIL);

      triton::arch::x86::x86_reg_rsp    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RSP);
      triton::arch::x86::x86_reg_esp    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_ESP);
      triton::arch::x86::x86_reg_sp     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_SP);
      triton::arch::x86::x86_reg_spl    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_SPL);
      triton::arch::x86::x86_reg_stack  = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RSP);

      triton::arch::x86::x86_reg_rbp    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RBP);
      triton::arch::x86::x86_reg_ebp    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EBP);
      triton::arch::x86::x86_reg_bp     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_BP);
      triton::arch::x86::x86_reg_bpl    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_BPL);

      triton::arch::x86::x86_reg_rip    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RIP);
      triton::arch::x86::x86_reg_eip    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EIP);
      triton::arch::x86::x86_reg_ip     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_IP);
      triton::arch::x86::x86_reg_pc     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RIP);

      triton::arch::x86::x86_reg_rflags = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RFLAGS);
      triton::arch::x86::x86_reg_flags  = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RFLAGS);

      triton::arch::x86::x86_reg_r8     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R8);
      triton::arch::x86::x86_reg_r8d    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R8D);
      triton::arch::x86::x86_reg_r8w    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R8W);
      triton::arch::x86::x86_reg_r8b    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R8B);

      triton::arch::x86::x86_reg_r9     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R9);
      triton::arch::x86::x86_reg_r9d    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R9D);
      triton::arch::x86::x86_reg_r9w    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R9W);
      triton::arch::x86::x86_reg_r9b    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R9B);

      triton::arch::x86::x86_reg_r10    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R10);
      triton::arch::x86::x86_reg_r10d   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R10D);
      triton::arch::x86::x86_reg_r10w   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R10W);
      triton::arch::x86::x86_reg_r10b   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R10B);

      triton::arch::x86::x86_reg_r11    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R11);
      triton::arch::x86::x86_reg_r11d   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R11D);
      triton::arch::x86::x86_reg_r11w   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R11W);
      triton::arch::x86::x86_reg_r11b   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R11B);

      triton::arch::x86::x86_reg_r12    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R12);
      triton::arch::x86::x86_reg_r12d   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R12D);
      triton::arch::x86::x86_reg_r12w   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R12W);
      triton::arch::x86::x86_reg_r12b   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R12B);

      triton::arch::x86::x86_reg_r13    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R13);
      triton::arch::x86::x86_reg_r13d   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R13D);
      triton::arch::x86::x86_reg_r13w   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R13W);
      triton::arch::x86::x86_reg_r13b   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R13B);

      triton::arch::x86::x86_reg_r14    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R14);
      triton::arch::x86::x86_reg_r14d   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R14D);
      triton::arch::x86::x86_reg_r14w   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R14W);
      triton::arch::x86::x86_reg_r14b   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R14B);

      triton::arch::x86::x86_reg_r15    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R15);
      triton::arch::x86::x86_reg_r15d   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R15D);
      triton::arch::x86::x86_reg_r15w   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R15W);
      triton::arch::x86::x86_reg_r15b   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R15B);

      triton::arch::x86::x86_reg_xmm0   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM0);
      triton::arch::x86::x86_reg_xmm1   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM1);
      triton::arch::x86::x86_reg_xmm2   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM2);
      triton::arch::x86::x86_reg_xmm3   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM3);
      triton::arch::x86::x86_reg_xmm4   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM4);
      triton::arch::x86::x86_reg_xmm5   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM5);
      triton::arch::x86::x86_reg_xmm6   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM6);
      triton::arch::x86::x86_reg_xmm7   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM7);
      triton::arch::x86::x86_reg_xmm8   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM8);
      triton::arch::x86::x86_reg_xmm9   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM9);
      triton::arch::x86::x86_reg_xmm10  = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM10);
      triton::arch::x86::x86_reg_xmm11  = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM11);
      triton::arch::x86::x86_reg_xmm12  = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM12);
      triton::arch::x86::x86_reg_xmm13  = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM13);
      triton::arch::x86::x86_reg_xmm14  = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM14);
      triton::arch::x86::x86_reg_xmm15  = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM15);

      triton::arch::x86::x86_reg_af     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_AF);
      triton::arch::x86::x86_reg_cf     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_CF);
      triton::arch::x86::x86_reg_df     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_DF);
      triton::arch::x86::x86_reg_if     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_IF);
      triton::arch::x86::x86_reg_of     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_OF);
      triton::arch::x86::x86_reg_pf     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_PF);
      triton::arch::x86::x86_reg_sf     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_SF);
      triton::arch::x86::x86_reg_tf     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_TF);
      triton::arch::x86::x86_reg_zf     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_ZF);

      /* Update python env ======================================================== */
      #ifdef TRITON_PYTHON_BINDINGS
        triton::bindings::python::initRegNamespace();
        triton::bindings::python::initCpuSizeNamespace();
        triton::bindings::python::initX86OpcodesNamespace();
        #ifdef __unix__
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
      memset(this->rflags,  0x00, sizeof(this->rflags));
      memset(this->r8,      0x00, sizeof(this->r8));
      memset(this->r9,      0x00, sizeof(this->r9));
      memset(this->r10,     0x00, sizeof(this->r10));
      memset(this->r11,     0x00, sizeof(this->r11));
      memset(this->r12,     0x00, sizeof(this->r12));
      memset(this->r13,     0x00, sizeof(this->r13));
      memset(this->r14,     0x00, sizeof(this->r14));
      memset(this->r15,     0x00, sizeof(this->r15));
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
    }


    void x8664Cpu::operator=(const x8664Cpu& other) {
      this->copy(other);
    }


    bool x8664Cpu::isFlag(triton::uint32 regId) {
      return ((regId >= triton::arch::x86::ID_REG_AF && regId <= triton::arch::x86::ID_REG_ZF) ? true : false);
    }


    bool x8664Cpu::isReg(triton::uint32 regId) {
      return ((regId >= triton::arch::x86::ID_REG_RAX && regId <= triton::arch::x86::ID_REG_XMM15) ? true : false);
    }


    bool x8664Cpu::isRegValid(triton::uint32 regId) {
      return (this->isFlag(regId) | this->isReg(regId));
    }


    bool x8664Cpu::isGPR(triton::uint32 regId) {
      return ((regId >= triton::arch::x86::ID_REG_RAX && regId < triton::arch::x86::ID_REG_XMM0) ? true : false);
    }


    bool x8664Cpu::isSSE(triton::uint32 regId) {
      return ((regId >= triton::arch::x86::ID_REG_XMM0 && regId <= triton::arch::x86::ID_REG_XMM15) ? true : false);
    }


    triton::uint32 x8664Cpu::invalidReg(void) {
      return triton::arch::x86::ID_REG_INVALID;
    }


    triton::uint32 x8664Cpu::numberOfReg(void) {
      return triton::arch::x86::ID_REG_LAST_ITEM;
    }


    triton::uint32 x8664Cpu::regSize(void) {
      return 8;
    }


    triton::uint32 x8664Cpu::regBitSize(void) {
      return 64;
    }


    std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> x8664Cpu::getRegInfo(triton::uint32 reg) {
      return triton::arch::x86::regIdToRegInfo(reg);
    }


    std::set<triton::arch::RegisterOperand*> x8664Cpu::getParentRegister(void) {
      std::set<triton::arch::RegisterOperand*> ret;
      ret.insert(&TRITON_X86_REG_RAX);
      ret.insert(&TRITON_X86_REG_RBX);
      ret.insert(&TRITON_X86_REG_RCX);
      ret.insert(&TRITON_X86_REG_RDX);
      ret.insert(&TRITON_X86_REG_RDI);
      ret.insert(&TRITON_X86_REG_RSI);
      ret.insert(&TRITON_X86_REG_RBP);
      ret.insert(&TRITON_X86_REG_RSP);
      ret.insert(&TRITON_X86_REG_RIP);
      ret.insert(&TRITON_X86_REG_RFLAGS);
      ret.insert(&TRITON_X86_REG_AF);
      ret.insert(&TRITON_X86_REG_CF);
      ret.insert(&TRITON_X86_REG_DF);
      ret.insert(&TRITON_X86_REG_IF);
      ret.insert(&TRITON_X86_REG_OF);
      ret.insert(&TRITON_X86_REG_PF);
      ret.insert(&TRITON_X86_REG_SF);
      ret.insert(&TRITON_X86_REG_TF);
      ret.insert(&TRITON_X86_REG_ZF);
      ret.insert(&TRITON_X86_REG_R8);
      ret.insert(&TRITON_X86_REG_R9);
      ret.insert(&TRITON_X86_REG_R10);
      ret.insert(&TRITON_X86_REG_R11);
      ret.insert(&TRITON_X86_REG_R12);
      ret.insert(&TRITON_X86_REG_R13);
      ret.insert(&TRITON_X86_REG_R14);
      ret.insert(&TRITON_X86_REG_R15);
      ret.insert(&TRITON_X86_REG_XMM0);
      ret.insert(&TRITON_X86_REG_XMM1);
      ret.insert(&TRITON_X86_REG_XMM2);
      ret.insert(&TRITON_X86_REG_XMM3);
      ret.insert(&TRITON_X86_REG_XMM4);
      ret.insert(&TRITON_X86_REG_XMM5);
      ret.insert(&TRITON_X86_REG_XMM6);
      ret.insert(&TRITON_X86_REG_XMM7);
      ret.insert(&TRITON_X86_REG_XMM8);
      ret.insert(&TRITON_X86_REG_XMM9);
      ret.insert(&TRITON_X86_REG_XMM10);
      ret.insert(&TRITON_X86_REG_XMM11);
      ret.insert(&TRITON_X86_REG_XMM12);
      ret.insert(&TRITON_X86_REG_XMM13);
      ret.insert(&TRITON_X86_REG_XMM14);
      ret.insert(&TRITON_X86_REG_XMM15);
      return ret;
    }


    void x8664Cpu::disassembly(triton::arch::Instruction &inst) {
      csh       handle;
      cs_insn*  insn;
      size_t    count;

      /* Check if the opcodes and opcodes' size are defined */
      if (inst.getOpcodes() == nullptr || inst.getOpcodesSize() == 0)
        throw std::runtime_error("x8664Cpu::disassembly(): Opcodes and opcodesSize must be definied.");

      /* Open capstone */
      if (cs_open(CS_ARCH_X86, CS_MODE_64, &handle) != CS_ERR_OK)
        throw std::runtime_error("x8664Cpu::disassembly(): Cannot open capstone.");

      /* Init capstone's options */
      cs_option(handle, CS_OPT_DETAIL, CS_OPT_ON);
      cs_option(handle, CS_OPT_SYNTAX, CS_OPT_SYNTAX_INTEL);

      /* Let's disass and build our operands */
      count = cs_disasm(handle, inst.getOpcodes(), inst.getOpcodesSize(), inst.getAddress(), 0, &insn);
      if (count > 0) {
        cs_detail* detail = insn->detail;
        for (triton::uint32 j = 0; j < count; j++) {

          /* Init the disassembly */
          std::stringstream str;
          str << insn[j].mnemonic << " " <<  insn[j].op_str;
          inst.setDisassembly(str.str());

          /* Init the instruction's type */
          inst.setType(capstoneInstToTritonInst(insn[j].id));

          /* Init operands */
          for (triton::uint32 n = 0; n < detail->x86.op_count; n++) {
            cs_x86_op *op = &(detail->x86.operands[n]);
            switch(op->type) {

              case X86_OP_IMM:
                inst.operands.push_back(triton::arch::OperandWrapper(triton::arch::ImmediateOperand(op->imm, op->size)));
                break;

              case X86_OP_MEM: {
                triton::arch::MemoryOperand mem = inst.popMemoryAccess();

                /* Set the size if the memory is not valid */
                if (!mem.isValid())
                  mem.setPair(std::make_pair(((op->size * BYTE_SIZE_BIT) - 1), 0));

                /* LEA if exists */
                triton::arch::RegisterOperand base(triton::arch::x86::capstoneRegToTritonReg(op->mem.base));
                triton::arch::RegisterOperand index(triton::arch::x86::capstoneRegToTritonReg(op->mem.index));
                triton::arch::ImmediateOperand disp(op->mem.disp, op->size);
                triton::arch::ImmediateOperand scale(op->mem.scale, op->size);

                /* Specify that LEA contains a PC relative */
                if (base == TRITON_X86_REG_PC)
                  mem.setPcRelative(inst.getNextAddress());

                mem.setBaseReg(base);
                mem.setIndexReg(index);
                mem.setDisplacement(disp);
                mem.setScale(scale);

                inst.operands.push_back(triton::arch::OperandWrapper(mem));
                break;
              }

              case X86_OP_REG:
                inst.operands.push_back(triton::arch::OperandWrapper(inst.getRegisterState(triton::arch::x86::capstoneRegToTritonReg(op->reg))));
                break;

              default:
                break;
            }
          }

        }
        /* Set branch */
        if (detail->groups_count > 0) {
          for (triton::uint32 n = 0; n < detail->groups_count; n++) {
            if (detail->groups[n] == X86_GRP_JUMP)
              inst.setBranch(true);
            if (detail->groups[n] == X86_GRP_JUMP || detail->groups[n] == X86_GRP_CALL || detail->groups[n] == X86_GRP_RET)
              inst.setControlFlow(true);
          }
        }
        /* Free capstone stuffs */
        cs_free(insn, count);
      }
      else
        throw std::runtime_error("x8664Cpu::disassembly(): Failed to disassemble the given code.");

      cs_close(&handle);
      return;
    }


    void x8664Cpu::buildSemantics(triton::arch::Instruction &inst) {
      if (!inst.getType())
        throw std::runtime_error("x8664Cpu::buildSemantics(): You must disassemble the instruction before.");
      triton::arch::x86::semantics::build(inst);
    }


    triton::uint8 x8664Cpu::getLastMemoryValue(triton::__uint addr) {
      if (this->memory.find(addr) == this->memory.end())
        return 0x00;
      return this->memory[addr];
    }


    triton::uint128 x8664Cpu::getLastMemoryValue(triton::arch::MemoryOperand& mem) {
      triton::uint128 ret = 0;
      triton::__uint addr = mem.getAddress();
      triton::uint32 size = mem.getSize();

      if (size == 0 || size > DQWORD_SIZE)
        throw std::invalid_argument("x8664Cpu::getLastMemoryValue(): Invalid size memory");

      for (triton::sint32 i = size-1; i >= 0; i--)
        ret = ((ret << BYTE_SIZE_BIT) | this->memory[addr+i]);

      return ret;
    }


    triton::uint128 x8664Cpu::getLastRegisterValue(triton::arch::RegisterOperand& reg) {
      triton::uint128 value = 0;
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

        case triton::arch::x86::ID_REG_RFLAGS: return (*((triton::uint64*)(this->rflags)));

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

        case triton::arch::x86::ID_REG_XMM0:  value = triton::fromBufferToUint128(this->xmm0); return value;
        case triton::arch::x86::ID_REG_XMM1:  value = triton::fromBufferToUint128(this->xmm1); return value;
        case triton::arch::x86::ID_REG_XMM2:  value = triton::fromBufferToUint128(this->xmm2); return value;
        case triton::arch::x86::ID_REG_XMM3:  value = triton::fromBufferToUint128(this->xmm3); return value;
        case triton::arch::x86::ID_REG_XMM4:  value = triton::fromBufferToUint128(this->xmm4); return value;
        case triton::arch::x86::ID_REG_XMM5:  value = triton::fromBufferToUint128(this->xmm5); return value;
        case triton::arch::x86::ID_REG_XMM6:  value = triton::fromBufferToUint128(this->xmm6); return value;
        case triton::arch::x86::ID_REG_XMM7:  value = triton::fromBufferToUint128(this->xmm7); return value;
        case triton::arch::x86::ID_REG_XMM8:  value = triton::fromBufferToUint128(this->xmm8); return value;
        case triton::arch::x86::ID_REG_XMM9:  value = triton::fromBufferToUint128(this->xmm9); return value;
        case triton::arch::x86::ID_REG_XMM10: value = triton::fromBufferToUint128(this->xmm10); return value;
        case triton::arch::x86::ID_REG_XMM11: value = triton::fromBufferToUint128(this->xmm11); return value;
        case triton::arch::x86::ID_REG_XMM12: value = triton::fromBufferToUint128(this->xmm12); return value;
        case triton::arch::x86::ID_REG_XMM13: value = triton::fromBufferToUint128(this->xmm13); return value;
        case triton::arch::x86::ID_REG_XMM14: value = triton::fromBufferToUint128(this->xmm14); return value;
        case triton::arch::x86::ID_REG_XMM15: value = triton::fromBufferToUint128(this->xmm15); return value;

        case triton::arch::x86::ID_REG_AF: return (((*((triton::uint64*)(this->rflags))) >> 4) & 1);
        case triton::arch::x86::ID_REG_CF: return ((*((triton::uint64*)(this->rflags))) & 1);
        case triton::arch::x86::ID_REG_DF: return (((*((triton::uint64*)(this->rflags))) >> 10) & 1);
        case triton::arch::x86::ID_REG_IF: return (((*((triton::uint64*)(this->rflags))) >> 9) & 1);
        case triton::arch::x86::ID_REG_OF: return (((*((triton::uint64*)(this->rflags))) >> 11) & 1);
        case triton::arch::x86::ID_REG_PF: return (((*((triton::uint64*)(this->rflags))) >> 2) & 1);
        case triton::arch::x86::ID_REG_SF: return (((*((triton::uint64*)(this->rflags))) >> 7) & 1);
        case triton::arch::x86::ID_REG_TF: return (((*((triton::uint64*)(this->rflags))) >> 8) & 1);
        case triton::arch::x86::ID_REG_ZF: return (((*((triton::uint64*)(this->rflags))) >> 6) & 1);

        default:
          throw std::invalid_argument("x8664Cpu::getLastRegisterValue(): Invalid register");
      }

      return value;
    }


    void x8664Cpu::setLastMemoryValue(triton::__uint addr, triton::uint8 value) {
      this->memory[addr] = value;
    }


    void x8664Cpu::setLastMemoryValue(triton::arch::MemoryOperand& mem) {
      triton::__uint addr = mem.getAddress();
      triton::uint32 size = mem.getSize();
      triton::uint128 cv  = mem.getConcreteValue();

      if (size == 0 || size > DQWORD_SIZE)
        throw std::invalid_argument("x8664Cpu::setLastMemoryValue(): Invalid size memory");

      for (triton::uint32 i = 0; i < size; i++) {
        this->memory[addr+i] = static_cast<triton::uint8>(cv & 0xff);
        cv >>= 8;
      }
    }


    void x8664Cpu::setLastRegisterValue(triton::arch::RegisterOperand& reg) {
      triton::uint128 value = reg.getConcreteValue();

      if (reg.isFlag())
        throw std::invalid_argument("x8664Cpu::setLastRegisterValue(): You cannot set an isolated flag. Use the flags register RFLAGS.");

      switch (reg.getId()) {
        case triton::arch::x86::ID_REG_RAX: (*((triton::uint64*)(this->rax)))  = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_EAX: (*((triton::uint32*)(this->rax)))  = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_AX:  (*((triton::uint16*)(this->rax)))  = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_AH:  (*((triton::uint8*)(this->rax+1))) = static_cast<triton::uint8>(value); break;
        case triton::arch::x86::ID_REG_AL:  (*((triton::uint8*)(this->rax)))   = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_RBX: (*((triton::uint64*)(this->rbx)))  = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_EBX: (*((triton::uint32*)(this->rbx)))  = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_BX:  (*((triton::uint16*)(this->rbx)))  = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_BH:  (*((triton::uint8*)(this->rbx+1))) = static_cast<triton::uint8>(value); break;
        case triton::arch::x86::ID_REG_BL:  (*((triton::uint8*)(this->rbx)))  = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_RCX: (*((triton::uint64*)(this->rcx)))  = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_ECX: (*((triton::uint32*)(this->rcx)))  = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_CX:  (*((triton::uint16*)(this->rcx)))  = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_CH:  (*((triton::uint8*)(this->rcx+1))) = static_cast<triton::uint8>(value); break;
        case triton::arch::x86::ID_REG_CL:  (*((triton::uint8*)(this->rcx)))   = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_RDX: (*((triton::uint64*)(this->rdx)))  = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_EDX: (*((triton::uint32*)(this->rdx)))  = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_DX:  (*((triton::uint16*)(this->rdx)))  = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_DH:  (*((triton::uint8*)(this->rdx+1))) = static_cast<triton::uint8>(value); break;
        case triton::arch::x86::ID_REG_DL:  (*((triton::uint8*)(this->rdx)))   = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_RDI: (*((triton::uint64*)(this->rdi)))  = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_EDI: (*((triton::uint32*)(this->rdi)))  = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_DI:  (*((triton::uint16*)(this->rdi)))  = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_DIL: (*((triton::uint8*)(this->rdi)))   = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_RSI: (*((triton::uint64*)(this->rsi))) = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_ESI: (*((triton::uint32*)(this->rsi))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_SI:  (*((triton::uint16*)(this->rsi))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_SIL: (*((triton::uint8*)(this->rsi)))  = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_RSP: (*((triton::uint64*)(this->rsp))) = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_ESP: (*((triton::uint32*)(this->rsp))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_SP:  (*((triton::uint16*)(this->rsp))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_SPL: (*((triton::uint8*)(this->rsp)))  = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_RBP: (*((triton::uint64*)(this->rbp))) = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_EBP: (*((triton::uint32*)(this->rbp))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_BP:  (*((triton::uint16*)(this->rbp))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_BPL: (*((triton::uint8*)(this->rbp)))  = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_RIP: (*((triton::uint64*)(this->rip))) = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_EIP: (*((triton::uint32*)(this->rip))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_IP:  (*((triton::uint16*)(this->rip))) = static_cast<triton::uint16>(value); break;

        case triton::arch::x86::ID_REG_RFLAGS: (*((triton::uint64*)(this->rflags))) = static_cast<triton::uint64>(value); break;

        case triton::arch::x86::ID_REG_R8:  (*((triton::uint64*)(this->r8))) = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_R8D: (*((triton::uint32*)(this->r8))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_R8W: (*((triton::uint16*)(this->r8))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_R8B: (*((triton::uint8*)(this->r8)))  = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_R9:  (*((triton::uint64*)(this->r9))) = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_R9D: (*((triton::uint32*)(this->r9))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_R9W: (*((triton::uint16*)(this->r9))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_R9B: (*((triton::uint8*)(this->r9)))  = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_R10:  (*((triton::uint64*)(this->r10))) = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_R10D: (*((triton::uint32*)(this->r10))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_R10W: (*((triton::uint16*)(this->r10))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_R10B: (*((triton::uint8*)(this->r10)))  = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_R11:  (*((triton::uint64*)(this->r11))) = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_R11D: (*((triton::uint32*)(this->r11))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_R11W: (*((triton::uint16*)(this->r11))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_R11B: (*((triton::uint8*)(this->r11)))  = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_R12:  (*((triton::uint64*)(this->r12))) = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_R12D: (*((triton::uint32*)(this->r12))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_R12W: (*((triton::uint16*)(this->r12))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_R12B: (*((triton::uint8*)(this->r12)))  = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_R13:  (*((triton::uint64*)(this->r13))) = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_R13D: (*((triton::uint32*)(this->r13))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_R13W: (*((triton::uint16*)(this->r13))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_R13B: (*((triton::uint8*)(this->r13)))  = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_R14:  (*((triton::uint64*)(this->r14))) = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_R14D: (*((triton::uint32*)(this->r14))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_R14W: (*((triton::uint16*)(this->r14))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_R14B: (*((triton::uint8*)(this->r14)))  = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_R15:  (*((triton::uint64*)(this->r15))) = static_cast<triton::uint64>(value); break;
        case triton::arch::x86::ID_REG_R15D: (*((triton::uint32*)(this->r15))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_R15W: (*((triton::uint16*)(this->r15))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_R15B: (*((triton::uint8*)(this->r15)))  = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_XMM0:  triton::fromUint128ToBuffer(value, this->xmm0); break;
        case triton::arch::x86::ID_REG_XMM1:  triton::fromUint128ToBuffer(value, this->xmm1); break;
        case triton::arch::x86::ID_REG_XMM2:  triton::fromUint128ToBuffer(value, this->xmm2); break;
        case triton::arch::x86::ID_REG_XMM3:  triton::fromUint128ToBuffer(value, this->xmm3); break;
        case triton::arch::x86::ID_REG_XMM4:  triton::fromUint128ToBuffer(value, this->xmm4); break;
        case triton::arch::x86::ID_REG_XMM5:  triton::fromUint128ToBuffer(value, this->xmm5); break;
        case triton::arch::x86::ID_REG_XMM6:  triton::fromUint128ToBuffer(value, this->xmm6); break;
        case triton::arch::x86::ID_REG_XMM7:  triton::fromUint128ToBuffer(value, this->xmm7); break;
        case triton::arch::x86::ID_REG_XMM8:  triton::fromUint128ToBuffer(value, this->xmm8); break;
        case triton::arch::x86::ID_REG_XMM9:  triton::fromUint128ToBuffer(value, this->xmm9); break;
        case triton::arch::x86::ID_REG_XMM10: triton::fromUint128ToBuffer(value, this->xmm10); break;
        case triton::arch::x86::ID_REG_XMM11: triton::fromUint128ToBuffer(value, this->xmm11); break;
        case triton::arch::x86::ID_REG_XMM12: triton::fromUint128ToBuffer(value, this->xmm12); break;
        case triton::arch::x86::ID_REG_XMM13: triton::fromUint128ToBuffer(value, this->xmm13); break;
        case triton::arch::x86::ID_REG_XMM14: triton::fromUint128ToBuffer(value, this->xmm14); break;
        case triton::arch::x86::ID_REG_XMM15: triton::fromUint128ToBuffer(value, this->xmm15); break;

        default:
          throw std::invalid_argument("x8664Cpu:setLastRegisterValue(): Invalid register");
      }
    }

    }; /* x86 namespace */
  }; /* arch namespace */
}; /* triton namespace */

