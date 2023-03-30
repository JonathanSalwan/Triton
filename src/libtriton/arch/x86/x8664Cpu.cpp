//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <algorithm>
#include <cctype>
#include <cstring>

#include <triton/architecture.hpp>
#include <triton/coreUtils.hpp>
#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/externalLibs.hpp>
#include <triton/immediate.hpp>
#include <triton/x8664Cpu.hpp>



namespace triton {
  namespace arch {
    namespace x86 {

      x8664Cpu::x8664Cpu(triton::callbacks::Callbacks* callbacks) : x86Specifications(ARCH_X86_64) {
        this->callbacks = callbacks;
        this->handle    = 0;

        this->clear();
        this->disassInit();
      }


      x8664Cpu::x8664Cpu(const x8664Cpu& other) : x86Specifications(ARCH_X86_64) {
        this->copy(other);
      }


      x8664Cpu::~x8664Cpu() {
        this->memory.clear();
        if (this->handle) {
          triton::extlibs::capstone::cs_close(&this->handle);
        }
      }


      void x8664Cpu::disassInit(void) {
        if (this->handle) {
          triton::extlibs::capstone::cs_close(&this->handle);
        }

        if (triton::extlibs::capstone::cs_open(triton::extlibs::capstone::CS_ARCH_X86, triton::extlibs::capstone::CS_MODE_64, &this->handle) != triton::extlibs::capstone::CS_ERR_OK)
          throw triton::exceptions::Disassembly("x8664Cpu::disassInit(): Cannot open capstone.");

        triton::extlibs::capstone::cs_option(this->handle, triton::extlibs::capstone::CS_OPT_DETAIL, triton::extlibs::capstone::CS_OPT_ON);
        triton::extlibs::capstone::cs_option(this->handle, triton::extlibs::capstone::CS_OPT_SYNTAX, triton::extlibs::capstone::CS_OPT_SYNTAX_INTEL);
      }


      void x8664Cpu::copy(const x8664Cpu& other) {
        this->callbacks = other.callbacks;
        this->memory    = other.memory;

        std::memcpy(this->rax,        other.rax,        sizeof(this->rax));
        std::memcpy(this->rbx,        other.rbx,        sizeof(this->rbx));
        std::memcpy(this->rcx,        other.rcx,        sizeof(this->rcx));
        std::memcpy(this->rdx,        other.rdx,        sizeof(this->rdx));
        std::memcpy(this->rdi,        other.rdi,        sizeof(this->rdi));
        std::memcpy(this->rsi,        other.rsi,        sizeof(this->rsi));
        std::memcpy(this->rsp,        other.rsp,        sizeof(this->rsp));
        std::memcpy(this->rbp,        other.rbp,        sizeof(this->rbp));
        std::memcpy(this->rip,        other.rip,        sizeof(this->rip));
        std::memcpy(this->eflags,     other.eflags,     sizeof(this->eflags));
        std::memcpy(this->r8,         other.r8,         sizeof(this->r8));
        std::memcpy(this->r9,         other.r9,         sizeof(this->r9));
        std::memcpy(this->r10,        other.r10,        sizeof(this->r10));
        std::memcpy(this->r11,        other.r11,        sizeof(this->r11));
        std::memcpy(this->r12,        other.r12,        sizeof(this->r12));
        std::memcpy(this->r13,        other.r13,        sizeof(this->r13));
        std::memcpy(this->r14,        other.r14,        sizeof(this->r14));
        std::memcpy(this->r15,        other.r15,        sizeof(this->r15));
        std::memcpy(this->st0,        other.st0,        sizeof(this->st0));
        std::memcpy(this->st1,        other.st1,        sizeof(this->st1));
        std::memcpy(this->st2,        other.st2,        sizeof(this->st2));
        std::memcpy(this->st3,        other.st3,        sizeof(this->st3));
        std::memcpy(this->st4,        other.st4,        sizeof(this->st4));
        std::memcpy(this->st5,        other.st5,        sizeof(this->st5));
        std::memcpy(this->st6,        other.st6,        sizeof(this->st6));
        std::memcpy(this->st7,        other.st7,        sizeof(this->st7));
        std::memcpy(this->zmm0,       other.zmm0,       sizeof(this->zmm0));
        std::memcpy(this->zmm1,       other.zmm1,       sizeof(this->zmm1));
        std::memcpy(this->zmm2,       other.zmm2,       sizeof(this->zmm2));
        std::memcpy(this->zmm3,       other.zmm3,       sizeof(this->zmm3));
        std::memcpy(this->zmm4,       other.zmm4,       sizeof(this->zmm4));
        std::memcpy(this->zmm5,       other.zmm5,       sizeof(this->zmm5));
        std::memcpy(this->zmm6,       other.zmm6,       sizeof(this->zmm6));
        std::memcpy(this->zmm7,       other.zmm7,       sizeof(this->zmm7));
        std::memcpy(this->zmm8,       other.zmm8,       sizeof(this->zmm8));
        std::memcpy(this->zmm9,       other.zmm9,       sizeof(this->zmm9));
        std::memcpy(this->zmm10,      other.zmm10,      sizeof(this->zmm10));
        std::memcpy(this->zmm11,      other.zmm11,      sizeof(this->zmm11));
        std::memcpy(this->zmm12,      other.zmm12,      sizeof(this->zmm12));
        std::memcpy(this->zmm13,      other.zmm13,      sizeof(this->zmm13));
        std::memcpy(this->zmm14,      other.zmm14,      sizeof(this->zmm14));
        std::memcpy(this->zmm15,      other.zmm15,      sizeof(this->zmm15));
        std::memcpy(this->zmm16,      other.zmm16,      sizeof(this->zmm16));
        std::memcpy(this->zmm17,      other.zmm17,      sizeof(this->zmm17));
        std::memcpy(this->zmm18,      other.zmm18,      sizeof(this->zmm18));
        std::memcpy(this->zmm19,      other.zmm19,      sizeof(this->zmm19));
        std::memcpy(this->zmm20,      other.zmm20,      sizeof(this->zmm20));
        std::memcpy(this->zmm21,      other.zmm21,      sizeof(this->zmm21));
        std::memcpy(this->zmm22,      other.zmm22,      sizeof(this->zmm22));
        std::memcpy(this->zmm23,      other.zmm23,      sizeof(this->zmm23));
        std::memcpy(this->zmm24,      other.zmm24,      sizeof(this->zmm24));
        std::memcpy(this->zmm25,      other.zmm25,      sizeof(this->zmm25));
        std::memcpy(this->zmm26,      other.zmm26,      sizeof(this->zmm26));
        std::memcpy(this->zmm27,      other.zmm27,      sizeof(this->zmm27));
        std::memcpy(this->zmm28,      other.zmm28,      sizeof(this->zmm28));
        std::memcpy(this->zmm29,      other.zmm29,      sizeof(this->zmm29));
        std::memcpy(this->zmm30,      other.zmm30,      sizeof(this->zmm30));
        std::memcpy(this->zmm31,      other.zmm31,      sizeof(this->zmm31));
        std::memcpy(this->mxcsr,      other.mxcsr,      sizeof(this->mxcsr));
        std::memcpy(this->cr0,        other.cr0,        sizeof(this->cr0));
        std::memcpy(this->cr1,        other.cr1,        sizeof(this->cr1));
        std::memcpy(this->cr2,        other.cr2,        sizeof(this->cr2));
        std::memcpy(this->cr3,        other.cr3,        sizeof(this->cr3));
        std::memcpy(this->cr4,        other.cr4,        sizeof(this->cr4));
        std::memcpy(this->cr5,        other.cr5,        sizeof(this->cr5));
        std::memcpy(this->cr6,        other.cr6,        sizeof(this->cr6));
        std::memcpy(this->cr7,        other.cr7,        sizeof(this->cr7));
        std::memcpy(this->cr8,        other.cr8,        sizeof(this->cr8));
        std::memcpy(this->cr9,        other.cr9,        sizeof(this->cr9));
        std::memcpy(this->cr10,       other.cr10,       sizeof(this->cr10));
        std::memcpy(this->cr11,       other.cr11,       sizeof(this->cr11));
        std::memcpy(this->cr12,       other.cr12,       sizeof(this->cr12));
        std::memcpy(this->cr13,       other.cr13,       sizeof(this->cr13));
        std::memcpy(this->cr14,       other.cr14,       sizeof(this->cr14));
        std::memcpy(this->cr15,       other.cr15,       sizeof(this->cr15));
        std::memcpy(this->cs,         other.cs,         sizeof(this->cs));
        std::memcpy(this->ds,         other.ds,         sizeof(this->ds));
        std::memcpy(this->es,         other.es,         sizeof(this->es));
        std::memcpy(this->fs,         other.fs,         sizeof(this->fs));
        std::memcpy(this->gs,         other.gs,         sizeof(this->gs));
        std::memcpy(this->ss,         other.ss,         sizeof(this->ss));
        std::memcpy(this->dr0,        other.dr0,        sizeof(this->dr0));
        std::memcpy(this->dr1,        other.dr1,        sizeof(this->dr1));
        std::memcpy(this->dr2,        other.dr2,        sizeof(this->dr2));
        std::memcpy(this->dr3,        other.dr3,        sizeof(this->dr3));
        std::memcpy(this->dr6,        other.dr6,        sizeof(this->dr6));
        std::memcpy(this->dr7,        other.dr7,        sizeof(this->dr7));
        std::memcpy(this->mxcsr_mask, other.mxcsr_mask, sizeof(this->mxcsr_mask));
        std::memcpy(this->fcw,        other.fcw,        sizeof(this->fcw));
        std::memcpy(this->fsw,        other.fsw,        sizeof(this->fsw));
        std::memcpy(this->ftw,        other.ftw,        sizeof(this->ftw));
        std::memcpy(this->fop,        other.fop,        sizeof(this->fop));
        std::memcpy(this->fip,        other.fip,        sizeof(this->fip));
        std::memcpy(this->fcs,        other.fcs,        sizeof(this->fcs));
        std::memcpy(this->fdp,        other.fdp,        sizeof(this->fdp));
        std::memcpy(this->fds,        other.fds,        sizeof(this->fds));
        std::memcpy(this->efer,       other.efer,       sizeof(this->efer));
        std::memcpy(this->tsc,        other.tsc,        sizeof(this->tsc));
      }


      void x8664Cpu::clear(void) {
        /* Clear memory */
        this->memory.clear();

        /* Clear registers */
        std::memset(this->rax,        0x00, sizeof(this->rax));
        std::memset(this->rbx,        0x00, sizeof(this->rbx));
        std::memset(this->rcx,        0x00, sizeof(this->rcx));
        std::memset(this->rdx,        0x00, sizeof(this->rdx));
        std::memset(this->rdi,        0x00, sizeof(this->rdi));
        std::memset(this->rsi,        0x00, sizeof(this->rsi));
        std::memset(this->rsp,        0x00, sizeof(this->rsp));
        std::memset(this->rbp,        0x00, sizeof(this->rbp));
        std::memset(this->rip,        0x00, sizeof(this->rip));
        std::memset(this->eflags,     0x00, sizeof(this->eflags));
        std::memset(this->r8,         0x00, sizeof(this->r8));
        std::memset(this->r9,         0x00, sizeof(this->r9));
        std::memset(this->r10,        0x00, sizeof(this->r10));
        std::memset(this->r11,        0x00, sizeof(this->r11));
        std::memset(this->r12,        0x00, sizeof(this->r12));
        std::memset(this->r13,        0x00, sizeof(this->r13));
        std::memset(this->r14,        0x00, sizeof(this->r14));
        std::memset(this->r15,        0x00, sizeof(this->r15));
        std::memset(this->st0,        0x00, sizeof(this->st0));
        std::memset(this->st1,        0x00, sizeof(this->st1));
        std::memset(this->st2,        0x00, sizeof(this->st2));
        std::memset(this->st3,        0x00, sizeof(this->st3));
        std::memset(this->st4,        0x00, sizeof(this->st4));
        std::memset(this->st5,        0x00, sizeof(this->st5));
        std::memset(this->st6,        0x00, sizeof(this->st6));
        std::memset(this->st7,        0x00, sizeof(this->st7));
        std::memset(this->zmm0,       0x00, sizeof(this->zmm0));
        std::memset(this->zmm1,       0x00, sizeof(this->zmm1));
        std::memset(this->zmm2,       0x00, sizeof(this->zmm2));
        std::memset(this->zmm3,       0x00, sizeof(this->zmm3));
        std::memset(this->zmm4,       0x00, sizeof(this->zmm4));
        std::memset(this->zmm5,       0x00, sizeof(this->zmm5));
        std::memset(this->zmm6,       0x00, sizeof(this->zmm6));
        std::memset(this->zmm7,       0x00, sizeof(this->zmm7));
        std::memset(this->zmm8,       0x00, sizeof(this->zmm8));
        std::memset(this->zmm9,       0x00, sizeof(this->zmm9));
        std::memset(this->zmm10,      0x00, sizeof(this->zmm10));
        std::memset(this->zmm11,      0x00, sizeof(this->zmm11));
        std::memset(this->zmm12,      0x00, sizeof(this->zmm12));
        std::memset(this->zmm13,      0x00, sizeof(this->zmm13));
        std::memset(this->zmm14,      0x00, sizeof(this->zmm14));
        std::memset(this->zmm15,      0x00, sizeof(this->zmm15));
        std::memset(this->zmm16,      0x00, sizeof(this->zmm16));
        std::memset(this->zmm17,      0x00, sizeof(this->zmm17));
        std::memset(this->zmm18,      0x00, sizeof(this->zmm18));
        std::memset(this->zmm19,      0x00, sizeof(this->zmm19));
        std::memset(this->zmm20,      0x00, sizeof(this->zmm20));
        std::memset(this->zmm21,      0x00, sizeof(this->zmm21));
        std::memset(this->zmm22,      0x00, sizeof(this->zmm22));
        std::memset(this->zmm23,      0x00, sizeof(this->zmm23));
        std::memset(this->zmm24,      0x00, sizeof(this->zmm24));
        std::memset(this->zmm25,      0x00, sizeof(this->zmm25));
        std::memset(this->zmm26,      0x00, sizeof(this->zmm26));
        std::memset(this->zmm27,      0x00, sizeof(this->zmm27));
        std::memset(this->zmm28,      0x00, sizeof(this->zmm28));
        std::memset(this->zmm29,      0x00, sizeof(this->zmm29));
        std::memset(this->zmm30,      0x00, sizeof(this->zmm30));
        std::memset(this->zmm31,      0x00, sizeof(this->zmm31));
        std::memset(this->mxcsr,      0x00, sizeof(this->mxcsr));
        std::memset(this->cr0,        0x00, sizeof(this->cr0));
        std::memset(this->cr1,        0x00, sizeof(this->cr1));
        std::memset(this->cr2,        0x00, sizeof(this->cr2));
        std::memset(this->cr3,        0x00, sizeof(this->cr3));
        std::memset(this->cr4,        0x00, sizeof(this->cr4));
        std::memset(this->cr5,        0x00, sizeof(this->cr5));
        std::memset(this->cr6,        0x00, sizeof(this->cr6));
        std::memset(this->cr7,        0x00, sizeof(this->cr7));
        std::memset(this->cr8,        0x00, sizeof(this->cr8));
        std::memset(this->cr9,        0x00, sizeof(this->cr9));
        std::memset(this->cr10,       0x00, sizeof(this->cr10));
        std::memset(this->cr11,       0x00, sizeof(this->cr11));
        std::memset(this->cr12,       0x00, sizeof(this->cr12));
        std::memset(this->cr13,       0x00, sizeof(this->cr13));
        std::memset(this->cr14,       0x00, sizeof(this->cr14));
        std::memset(this->cr15,       0x00, sizeof(this->cr15));
        std::memset(this->cs,         0x00, sizeof(this->cs));
        std::memset(this->ds,         0x00, sizeof(this->ds));
        std::memset(this->es,         0x00, sizeof(this->es));
        std::memset(this->fs,         0x00, sizeof(this->fs));
        std::memset(this->gs,         0x00, sizeof(this->gs));
        std::memset(this->ss,         0x00, sizeof(this->ss));
        std::memset(this->dr0,        0x00, sizeof(this->dr0));
        std::memset(this->dr1,        0x00, sizeof(this->dr1));
        std::memset(this->dr2,        0x00, sizeof(this->dr2));
        std::memset(this->dr3,        0x00, sizeof(this->dr3));
        std::memset(this->dr6,        0x00, sizeof(this->dr6));
        std::memset(this->dr7,        0x00, sizeof(this->dr7));
        std::memset(this->mxcsr_mask, 0x00, sizeof(this->mxcsr_mask));
        std::memset(this->fcw,        0x00, sizeof(this->fcw));
        std::memset(this->fsw,        0x00, sizeof(this->fsw));
        std::memset(this->ftw,        0x00, sizeof(this->ftw));
        std::memset(this->fop,        0x00, sizeof(this->fop));
        std::memset(this->fip,        0x00, sizeof(this->fip));
        std::memset(this->fcs,        0x00, sizeof(this->fcs));
        std::memset(this->fdp,        0x00, sizeof(this->fdp));
        std::memset(this->fds,        0x00, sizeof(this->fds));
        std::memset(this->efer,       0x00, sizeof(this->efer));
        std::memset(this->tsc,        0x00, sizeof(this->tsc));
      }


      x8664Cpu& x8664Cpu::operator=(const x8664Cpu& other) {
        this->copy(other);
        return *this;
      }


      triton::arch::endianness_e x8664Cpu::getEndianness(void) const {
        return triton::arch::LE_ENDIANNESS;
      }


      bool x8664Cpu::isFlag(triton::arch::register_e regId) const {
        if (regId >= triton::arch::ID_REG_X86_AC       && regId <= triton::arch::ID_REG_X86_ZF)       { return true; }
        if (regId >= triton::arch::ID_REG_X86_FTW      && regId <= triton::arch::ID_REG_X86_FDP)      { return true; }
        if (regId >= triton::arch::ID_REG_X86_SSE_IE   && regId <= triton::arch::ID_REG_X86_SSE_FZ)   { return true; }
        if (regId >= triton::arch::ID_REG_X86_FCW_IM   && regId <= triton::arch::ID_REG_X86_FCW_X)    { return true; }
        if (regId >= triton::arch::ID_REG_X86_FSW_IE   && regId <= triton::arch::ID_REG_X86_FSW_B)    { return true; }
        if (regId >= triton::arch::ID_REG_X86_EFER_TCE && regId <= triton::arch::ID_REG_X86_EFER_SCE) { return true; }

        return false;
      }


      bool x8664Cpu::isRegister(triton::arch::register_e regId) const {
        return (
          this->isGPR(regId)      ||
          this->isMMX(regId)      ||
          this->isSTX(regId)      ||
          this->isSSE(regId)      ||
          this->isFPU(regId)      ||
          this->isEFER(regId)     ||
          this->isTSC(regId)      ||
          this->isAVX256(regId)   ||
          this->isAVX512(regId)   ||
          this->isControl(regId)  ||
          this->isDebug(regId)    ||
          this->isSegment(regId)
        );
      }


      bool x8664Cpu::isRegisterValid(triton::arch::register_e regId) const {
        return (this->isFlag(regId) || this->isRegister(regId));
      }


      bool x8664Cpu::isGPR(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_RAX && regId <= triton::arch::ID_REG_X86_EFLAGS) ? true : false);
      }


      bool x8664Cpu::isMMX(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_MM0 && regId <= triton::arch::ID_REG_X86_MM7) ? true : false);
      }


      bool x8664Cpu::isSTX(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_ST0 && regId <= triton::arch::ID_REG_X86_ST7) ? true : false);
      }


      bool x8664Cpu::isSSE(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_MXCSR && regId <= triton::arch::ID_REG_X86_XMM15) ? true : false);
      }


      bool x8664Cpu::isFPU(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_FTW && regId <= triton::arch::ID_REG_X86_FDP) ? true : false);
      }


      bool x8664Cpu::isEFER(triton::arch::register_e regId) const {
        return ((regId == triton::arch::ID_REG_X86_EFER) ? true : false);
      }


      bool x8664Cpu::isTSC(triton::arch::register_e regId) const {
        return ((regId == triton::arch::ID_REG_X86_TSC) ? true : false);
      }


      bool x8664Cpu::isAVX256(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_YMM0 && regId <= triton::arch::ID_REG_X86_YMM15) ? true : false);
      }


      bool x8664Cpu::isAVX512(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_ZMM0 && regId <= triton::arch::ID_REG_X86_ZMM31) ? true : false);
      }


      bool x8664Cpu::isControl(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_CR0 && regId <= triton::arch::ID_REG_X86_CR15) ? true : false);
      }


      bool x8664Cpu::isDebug(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_DR0 && regId <= triton::arch::ID_REG_X86_DR7) ? true : false);
      }


      bool x8664Cpu::isSegment(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_CS && regId <= triton::arch::ID_REG_X86_SS) ? true : false);
      }


      triton::uint32 x8664Cpu::numberOfRegisters(void) const {
        return triton::arch::ID_REG_LAST_ITEM;
      }


      triton::uint32 x8664Cpu::gprSize(void) const {
        return triton::size::qword;
      }


      triton::uint32 x8664Cpu::gprBitSize(void) const {
        return triton::bitsize::qword;
      }


      const std::unordered_map<triton::arch::register_e, const triton::arch::Register>& x8664Cpu::getAllRegisters(void) const {
        return this->id2reg;
      }

      const std::unordered_map<triton::uint64, triton::uint8, IdentityHash<triton::uint64>>& x8664Cpu::getConcreteMemory(void) const {
        return this->memory;
      }


      std::set<const triton::arch::Register*> x8664Cpu::getParentRegisters(void) const {
        std::set<const triton::arch::Register*> ret;

        for (const auto& kv: this->id2reg) {
          auto regId = kv.first;
          const auto& reg = kv.second;

          /* Add GPR */
          if (reg.getSize() == this->gprSize())
            ret.insert(&reg);

          /* Add Flags */
          else if (this->isFlag(regId))
            ret.insert(&reg);

          /* Add STX */
          else if (this->isSTX(regId))
            ret.insert(&reg);

          /* Add SSE */
          else if (this->isSSE(regId))
            ret.insert(&reg);

          /* Add FPU */
          else if (this->isFPU(regId))
            ret.insert(&reg);

          /* Add EFER */
          else if (this->isEFER(regId))
            ret.insert(&reg);

          /* Add TSC */
          else if (this->isTSC(regId))
            ret.insert(&reg);

          /* Add AVX-256 */
          else if (this->isAVX256(regId))
            ret.insert(&reg);

          /* Add AVX-512 */
          else if (this->isAVX512(regId))
            ret.insert(&reg);

          /* Add Control */
          else if (this->isControl(regId))
            ret.insert(&reg);

          /* Add Debug */
          else if (this->isDebug(regId))
            ret.insert(&reg);

          /* Add Segment */
          else if (this->isSegment(regId))
            ret.insert(&reg);
        }

        return ret;
      }


      const triton::arch::Register& x8664Cpu::getRegister(triton::arch::register_e id) const {
        try {
          return this->id2reg.at(id);
        } catch (const std::out_of_range&) {
          throw triton::exceptions::Cpu("x8664Cpu::getRegister(): Invalid register for this architecture.");
        }
      }


      const triton::arch::Register& x8664Cpu::getRegister(const std::string& name) const {
        std::string lower = name;
        std::transform(lower.begin(), lower.end(), lower.begin(), [](unsigned char c){ return std::tolower(c); });
        try {
          return this->getRegister(this->name2id.at(lower));
        } catch (const std::out_of_range&) {
          throw triton::exceptions::Cpu("x8664Cpu::getRegister(): Invalid register for this architecture.");
        }
      }


      const triton::arch::Register& x8664Cpu::getParentRegister(const triton::arch::Register& reg) const {
        return this->getRegister(reg.getParent());
      }


      const triton::arch::Register& x8664Cpu::getParentRegister(triton::arch::register_e id) const {
        return this->getParentRegister(this->getRegister(id));
      }


      const triton::arch::Register& x8664Cpu::getProgramCounter(void) const {
        return this->getRegister(this->pcId);
      }


      const triton::arch::Register& x8664Cpu::getStackPointer(void) const {
        return this->getRegister(this->spId);
      }


      void x8664Cpu::disassembly(triton::arch::Instruction& inst) {
        triton::extlibs::capstone::cs_insn* insn;
        triton::usize count = 0;

        /* Check if the opcode and opcode' size are defined */
        if (inst.getOpcode() == nullptr || inst.getSize() == 0)
          throw triton::exceptions::Disassembly("x8664Cpu::disassembly(): Opcode and opcodeSize must be definied.");

        /* Clear instructicon's operands if alredy defined */
        inst.operands.clear();

        /* Update instruction address if undefined */
        if (!inst.getAddress()) {
          inst.setAddress(static_cast<triton::uint64>(this->getConcreteRegisterValue(this->getProgramCounter())));
        }

        /* Let's disass and build our operands */
        count = triton::extlibs::capstone::cs_disasm(this->handle, inst.getOpcode(), inst.getSize(), inst.getAddress(), 0, &insn);
        if (count > 0) {
          /* Detail information */
          triton::extlibs::capstone::cs_detail* detail = insn->detail;

          /* Init the disassembly */
          std::stringstream str;

          str << insn[0].mnemonic;
          if (detail->x86.op_count)
            str << " " <<  insn[0].op_str;

          inst.setDisassembly(str.str());

          /* Refine the size */
          inst.setSize(insn[0].size);

          /* Init the instruction's type */
          inst.setType(this->capstoneInstructionToTritonInstruction(insn[0].id));

          /* Init the instruction's prefix */
          inst.setPrefix(this->capstonePrefixToTritonPrefix(detail->x86.prefix[0]));

          /* Set architecture */
          inst.setArchitecture(triton::arch::ARCH_X86_64);

          /* Init operands */
          for (triton::uint32 n = 0; n < detail->x86.op_count; n++) {
            triton::extlibs::capstone::cs_x86_op* op = &(detail->x86.operands[n]);
            switch(op->type) {

              case triton::extlibs::capstone::X86_OP_IMM:
                inst.operands.push_back(triton::arch::OperandWrapper(triton::arch::Immediate(op->imm, op->size)));
                break;

              case triton::extlibs::capstone::X86_OP_MEM: {
                triton::arch::MemoryAccess mem;

                /* Set the size of the memory access */
                mem.setBits(((op->size * triton::bitsize::byte) - 1), 0);

                /* LEA if exists */
                const triton::arch::Register segment(*this, this->capstoneRegisterToTritonRegister(op->mem.segment));
                const triton::arch::Register base(*this, this->capstoneRegisterToTritonRegister(op->mem.base));
                const triton::arch::Register index(*this, this->capstoneRegisterToTritonRegister(op->mem.index));

                triton::uint32 immsize = (
                  this->isRegisterValid(base.getId()) ? base.getSize() :
                  this->isRegisterValid(index.getId()) ? index.getSize() :
                  this->gprSize()
                );

                triton::arch::Immediate disp(op->mem.disp, immsize);
                triton::arch::Immediate scale(op->mem.scale, immsize);

                /* Specify that LEA contains a PC relative */
                if (base.getId() == this->pcId)
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
                inst.operands.push_back(triton::arch::OperandWrapper(triton::arch::Register(*this, this->capstoneRegisterToTritonRegister(op->reg))));
                break;

              default:
                throw triton::exceptions::Disassembly("x8664Cpu::disassembly(): Invalid operand.");
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
      }


      triton::uint8 x8664Cpu::getConcreteMemoryValue(triton::uint64 addr, bool execCallbacks) const {
        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, triton::size::byte));

        auto it = this->memory.find(addr);
        if (it == this->memory.end()) {
          return 0x00;
        }

        return it->second;
      }


      triton::uint512 x8664Cpu::getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks) const {
        triton::uint512 ret = 0;
        triton::uint64 addr = 0;
        triton::uint32 size = 0;

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, mem);

        addr = mem.getAddress();
        size = mem.getSize();

        if (size == 0 || size > triton::size::dqqword)
          throw triton::exceptions::Cpu("x8664Cpu::getConcreteMemoryValue(): Invalid size memory.");

        for (triton::sint32 i = size-1; i >= 0; i--)
          ret = ((ret << triton::bitsize::byte) | this->getConcreteMemoryValue(addr+i, false));

        return ret;
      }


      std::vector<triton::uint8> x8664Cpu::getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks) const {
        std::vector<triton::uint8> area;

        for (triton::usize index = 0; index < size; index++)
          area.push_back(this->getConcreteMemoryValue(baseAddr+index, execCallbacks));

        return area;
      }


      triton::uint512 x8664Cpu::getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks) const {
        triton::uint512 value = 0;

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_REGISTER_VALUE, reg);

        switch (reg.getId()) {

          case triton::arch::ID_REG_X86_RAX: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->rax,  triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_EAX: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->rax,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_AX:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->rax,  triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_AH:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->rax+1, triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_AL:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->rax,   triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_RBX: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->rbx,  triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_EBX: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->rbx,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_BX:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->rbx,  triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_BH:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->rbx+1, triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_BL:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->rbx,   triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_RCX: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->rcx,  triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_ECX: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->rcx,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CX:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->rcx,  triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_CH:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->rcx+1, triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_CL:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->rcx,   triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_RDX: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->rdx,  triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_EDX: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->rdx,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_DX:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->rdx,  triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_DH:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->rdx+1, triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_DL:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->rdx,   triton::size::byte);  return val; }

          case triton::arch::ID_REG_X86_RDI: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->rdi, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_EDI: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->rdi, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_DI:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->rdi, triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_DIL: { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->rdi,  triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_RSI: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->rsi, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_ESI: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->rsi, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_SI:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->rsi, triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_SIL: { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->rsi,  triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_RSP: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->rsp, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_ESP: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->rsp, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_SP:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->rsp, triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_SPL: { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->rsp,  triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_RBP: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->rbp, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_EBP: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->rbp, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_BP:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->rbp, triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_BPL: { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->rbp,  triton::size::byte);  return val; }

          case triton::arch::ID_REG_X86_RIP: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->rip, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_EIP: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->rip, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_IP:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->rip, triton::size::word);  return val; }

          case triton::arch::ID_REG_X86_EFLAGS: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return val; }

          case triton::arch::ID_REG_X86_R8:   { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->r8, triton::size::qword);  return val; }
          case triton::arch::ID_REG_X86_R8D:  { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->r8, triton::size::dword);  return val; }
          case triton::arch::ID_REG_X86_R8W:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->r8, triton::size::word);   return val; }
          case triton::arch::ID_REG_X86_R8B:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->r8,  triton::size::byte);   return val; }
          case triton::arch::ID_REG_X86_R9:   { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->r9, triton::size::qword);  return val; }
          case triton::arch::ID_REG_X86_R9D:  { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->r9, triton::size::dword);  return val; }
          case triton::arch::ID_REG_X86_R9W:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->r9, triton::size::word);   return val; }
          case triton::arch::ID_REG_X86_R9B:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->r9,  triton::size::byte);   return val; }
          case triton::arch::ID_REG_X86_R10:  { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->r10, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_R10D: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->r10, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_R10W: { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->r10, triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_R10B: { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->r10,  triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_R11:  { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->r11, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_R11D: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->r11, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_R11W: { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->r11, triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_R11B: { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->r11,  triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_R12:  { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->r12, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_R12D: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->r12, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_R12W: { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->r12, triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_R12B: { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->r12,  triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_R13:  { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->r13, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_R13D: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->r13, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_R13W: { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->r13, triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_R13B: { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->r13,  triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_R14:  { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->r14, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_R14D: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->r14, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_R14W: { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->r14, triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_R14B: { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->r14,  triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_R15:  { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->r15, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_R15D: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->r15, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_R15W: { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->r15, triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_R15B: { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->r15,  triton::size::byte);  return val; }

          case triton::arch::ID_REG_X86_MM0: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->st0, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_MM1: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->st1, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_MM2: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->st2, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_MM3: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->st3, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_MM4: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->st4, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_MM5: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->st5, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_MM6: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->st6, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_MM7: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->st7, triton::size::qword); return val; }

          case triton::arch::ID_REG_X86_ST0: { return triton::utils::cast<triton::uint512>(triton::utils::cast<triton::uint80>(this->st0)); }
          case triton::arch::ID_REG_X86_ST1: { return triton::utils::cast<triton::uint512>(triton::utils::cast<triton::uint80>(this->st1)); }
          case triton::arch::ID_REG_X86_ST2: { return triton::utils::cast<triton::uint512>(triton::utils::cast<triton::uint80>(this->st2)); }
          case triton::arch::ID_REG_X86_ST3: { return triton::utils::cast<triton::uint512>(triton::utils::cast<triton::uint80>(this->st3)); }
          case triton::arch::ID_REG_X86_ST4: { return triton::utils::cast<triton::uint512>(triton::utils::cast<triton::uint80>(this->st4)); }
          case triton::arch::ID_REG_X86_ST5: { return triton::utils::cast<triton::uint512>(triton::utils::cast<triton::uint80>(this->st5)); }
          case triton::arch::ID_REG_X86_ST6: { return triton::utils::cast<triton::uint512>(triton::utils::cast<triton::uint80>(this->st6)); }
          case triton::arch::ID_REG_X86_ST7: { return triton::utils::cast<triton::uint512>(triton::utils::cast<triton::uint80>(this->st7)); }

          case triton::arch::ID_REG_X86_XMM0:  { return triton::utils::cast<triton::uint128>(this->zmm0);  }
          case triton::arch::ID_REG_X86_XMM1:  { return triton::utils::cast<triton::uint128>(this->zmm1);  }
          case triton::arch::ID_REG_X86_XMM2:  { return triton::utils::cast<triton::uint128>(this->zmm2);  }
          case triton::arch::ID_REG_X86_XMM3:  { return triton::utils::cast<triton::uint128>(this->zmm3);  }
          case triton::arch::ID_REG_X86_XMM4:  { return triton::utils::cast<triton::uint128>(this->zmm4);  }
          case triton::arch::ID_REG_X86_XMM5:  { return triton::utils::cast<triton::uint128>(this->zmm5);  }
          case triton::arch::ID_REG_X86_XMM6:  { return triton::utils::cast<triton::uint128>(this->zmm6);  }
          case triton::arch::ID_REG_X86_XMM7:  { return triton::utils::cast<triton::uint128>(this->zmm7);  }
          case triton::arch::ID_REG_X86_XMM8:  { return triton::utils::cast<triton::uint128>(this->zmm8);  }
          case triton::arch::ID_REG_X86_XMM9:  { return triton::utils::cast<triton::uint128>(this->zmm9);  }
          case triton::arch::ID_REG_X86_XMM10: { return triton::utils::cast<triton::uint128>(this->zmm10); }
          case triton::arch::ID_REG_X86_XMM11: { return triton::utils::cast<triton::uint128>(this->zmm11); }
          case triton::arch::ID_REG_X86_XMM12: { return triton::utils::cast<triton::uint128>(this->zmm12); }
          case triton::arch::ID_REG_X86_XMM13: { return triton::utils::cast<triton::uint128>(this->zmm13); }
          case triton::arch::ID_REG_X86_XMM14: { return triton::utils::cast<triton::uint128>(this->zmm14); }
          case triton::arch::ID_REG_X86_XMM15: { return triton::utils::cast<triton::uint128>(this->zmm15); }

          case triton::arch::ID_REG_X86_YMM0:  { return triton::utils::cast<triton::uint256>(this->zmm0);  }
          case triton::arch::ID_REG_X86_YMM1:  { return triton::utils::cast<triton::uint256>(this->zmm1);  }
          case triton::arch::ID_REG_X86_YMM2:  { return triton::utils::cast<triton::uint256>(this->zmm2);  }
          case triton::arch::ID_REG_X86_YMM3:  { return triton::utils::cast<triton::uint256>(this->zmm3);  }
          case triton::arch::ID_REG_X86_YMM4:  { return triton::utils::cast<triton::uint256>(this->zmm4);  }
          case triton::arch::ID_REG_X86_YMM5:  { return triton::utils::cast<triton::uint256>(this->zmm5);  }
          case triton::arch::ID_REG_X86_YMM6:  { return triton::utils::cast<triton::uint256>(this->zmm6);  }
          case triton::arch::ID_REG_X86_YMM7:  { return triton::utils::cast<triton::uint256>(this->zmm7);  }
          case triton::arch::ID_REG_X86_YMM8:  { return triton::utils::cast<triton::uint256>(this->zmm8);  }
          case triton::arch::ID_REG_X86_YMM9:  { return triton::utils::cast<triton::uint256>(this->zmm9);  }
          case triton::arch::ID_REG_X86_YMM10: { return triton::utils::cast<triton::uint256>(this->zmm10); }
          case triton::arch::ID_REG_X86_YMM11: { return triton::utils::cast<triton::uint256>(this->zmm11); }
          case triton::arch::ID_REG_X86_YMM12: { return triton::utils::cast<triton::uint256>(this->zmm12); }
          case triton::arch::ID_REG_X86_YMM13: { return triton::utils::cast<triton::uint256>(this->zmm13); }
          case triton::arch::ID_REG_X86_YMM14: { return triton::utils::cast<triton::uint256>(this->zmm14); }
          case triton::arch::ID_REG_X86_YMM15: { return triton::utils::cast<triton::uint256>(this->zmm15); }

          case triton::arch::ID_REG_X86_ZMM0:  { return triton::utils::cast<triton::uint512>(this->zmm0);  }
          case triton::arch::ID_REG_X86_ZMM1:  { return triton::utils::cast<triton::uint512>(this->zmm1);  }
          case triton::arch::ID_REG_X86_ZMM2:  { return triton::utils::cast<triton::uint512>(this->zmm2);  }
          case triton::arch::ID_REG_X86_ZMM3:  { return triton::utils::cast<triton::uint512>(this->zmm3);  }
          case triton::arch::ID_REG_X86_ZMM4:  { return triton::utils::cast<triton::uint512>(this->zmm4);  }
          case triton::arch::ID_REG_X86_ZMM5:  { return triton::utils::cast<triton::uint512>(this->zmm5);  }
          case triton::arch::ID_REG_X86_ZMM6:  { return triton::utils::cast<triton::uint512>(this->zmm6);  }
          case triton::arch::ID_REG_X86_ZMM7:  { return triton::utils::cast<triton::uint512>(this->zmm7);  }
          case triton::arch::ID_REG_X86_ZMM8:  { return triton::utils::cast<triton::uint512>(this->zmm8);  }
          case triton::arch::ID_REG_X86_ZMM9:  { return triton::utils::cast<triton::uint512>(this->zmm9);  }
          case triton::arch::ID_REG_X86_ZMM10: { return triton::utils::cast<triton::uint512>(this->zmm10); }
          case triton::arch::ID_REG_X86_ZMM11: { return triton::utils::cast<triton::uint512>(this->zmm11); }
          case triton::arch::ID_REG_X86_ZMM12: { return triton::utils::cast<triton::uint512>(this->zmm12); }
          case triton::arch::ID_REG_X86_ZMM13: { return triton::utils::cast<triton::uint512>(this->zmm13); }
          case triton::arch::ID_REG_X86_ZMM14: { return triton::utils::cast<triton::uint512>(this->zmm14); }
          case triton::arch::ID_REG_X86_ZMM15: { return triton::utils::cast<triton::uint512>(this->zmm15); }
          case triton::arch::ID_REG_X86_ZMM16: { return triton::utils::cast<triton::uint512>(this->zmm16); }
          case triton::arch::ID_REG_X86_ZMM17: { return triton::utils::cast<triton::uint512>(this->zmm17); }
          case triton::arch::ID_REG_X86_ZMM18: { return triton::utils::cast<triton::uint512>(this->zmm18); }
          case triton::arch::ID_REG_X86_ZMM19: { return triton::utils::cast<triton::uint512>(this->zmm19); }
          case triton::arch::ID_REG_X86_ZMM20: { return triton::utils::cast<triton::uint512>(this->zmm20); }
          case triton::arch::ID_REG_X86_ZMM21: { return triton::utils::cast<triton::uint512>(this->zmm21); }
          case triton::arch::ID_REG_X86_ZMM22: { return triton::utils::cast<triton::uint512>(this->zmm22); }
          case triton::arch::ID_REG_X86_ZMM23: { return triton::utils::cast<triton::uint512>(this->zmm23); }
          case triton::arch::ID_REG_X86_ZMM24: { return triton::utils::cast<triton::uint512>(this->zmm24); }
          case triton::arch::ID_REG_X86_ZMM25: { return triton::utils::cast<triton::uint512>(this->zmm25); }
          case triton::arch::ID_REG_X86_ZMM26: { return triton::utils::cast<triton::uint512>(this->zmm26); }
          case triton::arch::ID_REG_X86_ZMM27: { return triton::utils::cast<triton::uint512>(this->zmm27); }
          case triton::arch::ID_REG_X86_ZMM28: { return triton::utils::cast<triton::uint512>(this->zmm28); }
          case triton::arch::ID_REG_X86_ZMM29: { return triton::utils::cast<triton::uint512>(this->zmm29); }
          case triton::arch::ID_REG_X86_ZMM30: { return triton::utils::cast<triton::uint512>(this->zmm30); }
          case triton::arch::ID_REG_X86_ZMM31: { return triton::utils::cast<triton::uint512>(this->zmm31); }


          case triton::arch::ID_REG_X86_TSC:        { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->tsc,        sizeof(triton::uint64)); return val; }
          case triton::arch::ID_REG_X86_MXCSR:      { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->mxcsr,      sizeof(triton::uint32)); return val; }
          case triton::arch::ID_REG_X86_MXCSR_MASK: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->mxcsr_mask, sizeof(triton::uint32)); return val; }

          case triton::arch::ID_REG_X86_CR0:  { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cr0,  triton::size::qword); return val;  }
          case triton::arch::ID_REG_X86_CR1:  { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cr1,  triton::size::qword); return val;  }
          case triton::arch::ID_REG_X86_CR2:  { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cr2,  triton::size::qword); return val;  }
          case triton::arch::ID_REG_X86_CR3:  { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cr3,  triton::size::qword); return val;  }
          case triton::arch::ID_REG_X86_CR4:  { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cr4,  triton::size::qword); return val;  }
          case triton::arch::ID_REG_X86_CR5:  { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cr5,  triton::size::qword); return val;  }
          case triton::arch::ID_REG_X86_CR6:  { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cr6,  triton::size::qword); return val;  }
          case triton::arch::ID_REG_X86_CR7:  { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cr7,  triton::size::qword); return val;  }
          case triton::arch::ID_REG_X86_CR8:  { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cr8,  triton::size::qword); return val;  }
          case triton::arch::ID_REG_X86_CR9:  { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cr9,  triton::size::qword); return val;  }
          case triton::arch::ID_REG_X86_CR10: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cr10, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_CR11: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cr11, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_CR12: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cr12, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_CR13: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cr13, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_CR14: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cr14, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_CR15: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cr15, triton::size::qword); return val; }

          case triton::arch::ID_REG_X86_DR0: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->dr0, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_DR1: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->dr1, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_DR2: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->dr2, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_DR3: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->dr3, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_DR6: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->dr6, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_DR7: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->dr7, triton::size::qword); return val; }

          case triton::arch::ID_REG_X86_SSE_IE:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32)); return ((flag >> 0) & 1);  }
          case triton::arch::ID_REG_X86_SSE_DE:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32)); return ((flag >> 1) & 1);  }
          case triton::arch::ID_REG_X86_SSE_ZE:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32)); return ((flag >> 2) & 1);  }
          case triton::arch::ID_REG_X86_SSE_OE:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32)); return ((flag >> 3) & 1);  }
          case triton::arch::ID_REG_X86_SSE_UE:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32)); return ((flag >> 4) & 1);  }
          case triton::arch::ID_REG_X86_SSE_PE:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32)); return ((flag >> 5) & 1);  }
          case triton::arch::ID_REG_X86_SSE_DAZ: { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32)); return ((flag >> 6) & 1);  }
          case triton::arch::ID_REG_X86_SSE_IM:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32)); return ((flag >> 7) & 1);  }
          case triton::arch::ID_REG_X86_SSE_DM:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32)); return ((flag >> 8) & 1);  }
          case triton::arch::ID_REG_X86_SSE_ZM:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32)); return ((flag >> 9) & 1);  }
          case triton::arch::ID_REG_X86_SSE_OM:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32)); return ((flag >> 10) & 1); }
          case triton::arch::ID_REG_X86_SSE_UM:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32)); return ((flag >> 11) & 1); }
          case triton::arch::ID_REG_X86_SSE_PM:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32)); return ((flag >> 12) & 1); }
          case triton::arch::ID_REG_X86_SSE_RL:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32)); return ((flag >> 13) & 1); }
          case triton::arch::ID_REG_X86_SSE_RH:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32)); return ((flag >> 14) & 1); }
          case triton::arch::ID_REG_X86_SSE_FZ:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32)); return ((flag >> 15) & 1); }

          case triton::arch::ID_REG_X86_CF:  { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return ((flag >> 0) & 1);  }
          case triton::arch::ID_REG_X86_PF:  { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return ((flag >> 2) & 1);  }
          case triton::arch::ID_REG_X86_AF:  { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return ((flag >> 4) & 1);  }
          case triton::arch::ID_REG_X86_ZF:  { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return ((flag >> 6) & 1);  }
          case triton::arch::ID_REG_X86_SF:  { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return ((flag >> 7) & 1);  }
          case triton::arch::ID_REG_X86_TF:  { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return ((flag >> 8) & 1);  }
          case triton::arch::ID_REG_X86_IF:  { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return ((flag >> 9) & 1);  }
          case triton::arch::ID_REG_X86_DF:  { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return ((flag >> 10) & 1); }
          case triton::arch::ID_REG_X86_OF:  { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return ((flag >> 11) & 1); }
          case triton::arch::ID_REG_X86_NT:  { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return ((flag >> 14) & 1); }
          case triton::arch::ID_REG_X86_RF:  { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return ((flag >> 16) & 1); }
          case triton::arch::ID_REG_X86_VM:  { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return ((flag >> 17) & 1); }
          case triton::arch::ID_REG_X86_AC:  { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return ((flag >> 18) & 1); }
          case triton::arch::ID_REG_X86_VIF: { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return ((flag >> 19) & 1); }
          case triton::arch::ID_REG_X86_VIP: { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return ((flag >> 20) & 1); }
          case triton::arch::ID_REG_X86_ID:  { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64)); return ((flag >> 21) & 1); }

          case triton::arch::ID_REG_X86_CS: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->cs, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_DS: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->ds, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_ES: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->es, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_FS: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->fs, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_GS: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->gs, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_SS: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->ss, triton::size::qword); return val; }

          case triton::arch::ID_REG_X86_FIP: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->fip, sizeof(triton::uint64)); return val; }
          case triton::arch::ID_REG_X86_FDP: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->fdp, sizeof(triton::uint64)); return val; }
          case triton::arch::ID_REG_X86_FCW: { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->fcw, sizeof(triton::uint16)); return val; }
          case triton::arch::ID_REG_X86_FSW: { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->fsw, sizeof(triton::uint16)); return val; }
          case triton::arch::ID_REG_X86_FOP: { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->fop, sizeof(triton::uint16)); return val; }
          case triton::arch::ID_REG_X86_FCS: { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->fcs, sizeof(triton::uint16)); return val; }
          case triton::arch::ID_REG_X86_FDS: { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->fds, sizeof(triton::uint16)); return val; }
          case triton::arch::ID_REG_X86_FTW: { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->ftw, sizeof(triton::uint16)); return val; }

          case triton::arch::ID_REG_X86_FCW_IM: { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16)); return ((flag >> 0) & 1);  }
          case triton::arch::ID_REG_X86_FCW_DM: { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16)); return ((flag >> 1) & 1);  }
          case triton::arch::ID_REG_X86_FCW_ZM: { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16)); return ((flag >> 2) & 1);  }
          case triton::arch::ID_REG_X86_FCW_OM: { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16)); return ((flag >> 3) & 1);  }
          case triton::arch::ID_REG_X86_FCW_UM: { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16)); return ((flag >> 4) & 1);  }
          case triton::arch::ID_REG_X86_FCW_PM: { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16)); return ((flag >> 5) & 1);  }
          case triton::arch::ID_REG_X86_FCW_PC: { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16)); return ((flag >> 8) & 3);  }
          case triton::arch::ID_REG_X86_FCW_RC: { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16)); return ((flag >> 10) & 3); }
          case triton::arch::ID_REG_X86_FCW_X:  { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16)); return ((flag >> 12) & 1); }

          case triton::arch::ID_REG_X86_FSW_IE:  { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16)); return ((flag >> 0) & 1);  }
          case triton::arch::ID_REG_X86_FSW_DE:  { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16)); return ((flag >> 1) & 1);  }
          case triton::arch::ID_REG_X86_FSW_ZE:  { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16)); return ((flag >> 2) & 1);  }
          case triton::arch::ID_REG_X86_FSW_OE:  { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16)); return ((flag >> 3) & 1);  }
          case triton::arch::ID_REG_X86_FSW_UE:  { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16)); return ((flag >> 4) & 1);  }
          case triton::arch::ID_REG_X86_FSW_PE:  { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16)); return ((flag >> 5) & 1);  }
          case triton::arch::ID_REG_X86_FSW_SF:  { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16)); return ((flag >> 6) & 1);  }
          case triton::arch::ID_REG_X86_FSW_ES:  { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16)); return ((flag >> 7) & 1);  }
          case triton::arch::ID_REG_X86_FSW_C0:  { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16)); return ((flag >> 8) & 1);  }
          case triton::arch::ID_REG_X86_FSW_C1:  { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16)); return ((flag >> 9) & 1);  }
          case triton::arch::ID_REG_X86_FSW_C2:  { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16)); return ((flag >> 10) & 1); }
          case triton::arch::ID_REG_X86_FSW_TOP: { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16)); return ((flag >> 11) & 7); }
          case triton::arch::ID_REG_X86_FSW_C3:  { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16)); return ((flag >> 14) & 1); }
          case triton::arch::ID_REG_X86_FSW_B:   { triton::uint16 flag = 0; std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16)); return ((flag >> 15) & 1); }

          case triton::arch::ID_REG_X86_EFER_SCE:   { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64)); return ((flag >> 0) & 1);  }
          case triton::arch::ID_REG_X86_EFER_LME:   { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64)); return ((flag >> 8) & 1);  }
          case triton::arch::ID_REG_X86_EFER_LMA:   { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64)); return ((flag >> 10) & 1); }
          case triton::arch::ID_REG_X86_EFER_NXE:   { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64)); return ((flag >> 11) & 1); }
          case triton::arch::ID_REG_X86_EFER_SVME:  { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64)); return ((flag >> 12) & 1); }
          case triton::arch::ID_REG_X86_EFER_LMSLE: { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64)); return ((flag >> 13) & 1); }
          case triton::arch::ID_REG_X86_EFER_FFXSR: { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64)); return ((flag >> 14) & 1); }
          case triton::arch::ID_REG_X86_EFER_TCE:   { triton::uint64 flag = 0; std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64)); return ((flag >> 15) & 1); }
          case triton::arch::ID_REG_X86_EFER:       { triton::uint64 val = 0;  std::memcpy(&val,  (triton::uint64*)this->efer, sizeof(triton::uint64)); return val; }

          default:
            throw triton::exceptions::Cpu("x8664Cpu::getConcreteRegisterValue(): Invalid register.");
        }

        return value;
      }


      void x8664Cpu::setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value, bool execCallbacks) {
        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, triton::size::byte), value);
        this->memory[addr] = value;
      }


      void x8664Cpu::setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value, bool execCallbacks) {
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();
        triton::uint512 cv  = value;

        if (cv > mem.getMaxValue())
          throw triton::exceptions::Register("x8664Cpu::setConcreteMemoryValue(): You cannot set this concrete value (too big) to this memory access.");

        if (size == 0 || size > triton::size::dqqword)
          throw triton::exceptions::Cpu("x8664Cpu::setConcreteMemoryValue(): Invalid size memory.");

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, mem, value);

        for (triton::uint32 i = 0; i < size; i++) {
          this->memory[addr+i] = static_cast<triton::uint8>((cv & 0xff));
          cv >>= 8;
        }
      }


      void x8664Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values, bool execCallbacks) {
        // Pre-reserving the memory. We modified the original robin_map to not force rehash on reserve.
        this->memory.reserve(values.size() + this->memory.size());
        for (triton::usize index = 0; index < values.size(); index++) {
          this->setConcreteMemoryValue(baseAddr+index, values[index], execCallbacks);
        }
      }


      void x8664Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const void* area, triton::usize size, bool execCallbacks) {
        // Pre-reserving the memory. We modified the original robin_map to not force rehash on every reserve if not needed.
        this->memory.reserve(size + this->memory.size());
        for (triton::usize index = 0; index < size; index++) {
          this->setConcreteMemoryValue(baseAddr+index, reinterpret_cast<const triton::uint8*>(area)[index], execCallbacks);
        }
      }


      void x8664Cpu::setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value, bool execCallbacks) {
        if (value > reg.getMaxValue())
          throw triton::exceptions::Register("x8664Cpu::setConcreteRegisterValue(): You cannot set this concrete value (too big) to this register.");

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_REGISTER_VALUE, reg, value);

        switch (reg.getId()) {

          case triton::arch::ID_REG_X86_RAX: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->rax,    &val, triton::size::qword);  break; }
          case triton::arch::ID_REG_X86_EAX: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->rax,    &val, triton::size::dword);  break; }
          case triton::arch::ID_REG_X86_AX:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->rax,    &val, triton::size::word);   break; }
          case triton::arch::ID_REG_X86_AH:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)(this->rax+1), &val, triton::size::byte);   break; }
          case triton::arch::ID_REG_X86_AL:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->rax,     &val, triton::size::byte);   break; }
          case triton::arch::ID_REG_X86_RBX: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->rbx,    &val, triton::size::qword);  break; }
          case triton::arch::ID_REG_X86_EBX: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->rbx,    &val, triton::size::dword);  break; }
          case triton::arch::ID_REG_X86_BX:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->rbx,    &val, triton::size::word);   break; }
          case triton::arch::ID_REG_X86_BH:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)(this->rbx+1), &val, triton::size::byte);   break; }
          case triton::arch::ID_REG_X86_BL:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->rbx,     &val, triton::size::byte);   break; }
          case triton::arch::ID_REG_X86_RCX: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->rcx,    &val, triton::size::qword);  break; }
          case triton::arch::ID_REG_X86_ECX: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->rcx,    &val, triton::size::dword);  break; }
          case triton::arch::ID_REG_X86_CX:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->rcx,    &val, triton::size::word);   break; }
          case triton::arch::ID_REG_X86_CH:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)(this->rcx+1), &val, triton::size::byte);   break; }
          case triton::arch::ID_REG_X86_CL:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->rcx,     &val, triton::size::byte);   break; }
          case triton::arch::ID_REG_X86_RDX: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->rdx,    &val, triton::size::qword);  break; }
          case triton::arch::ID_REG_X86_EDX: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->rdx,    &val, triton::size::dword);  break; }
          case triton::arch::ID_REG_X86_DX:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->rdx,    &val, triton::size::word);   break; }
          case triton::arch::ID_REG_X86_DH:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)(this->rdx+1), &val, triton::size::byte);   break; }
          case triton::arch::ID_REG_X86_DL:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->rdx,     &val, triton::size::byte);   break; }

          case triton::arch::ID_REG_X86_RDI: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->rdi, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_EDI: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->rdi, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_DI:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->rdi, &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_DIL: { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->rdi,  &val, triton::size::byte);  break; }
          case triton::arch::ID_REG_X86_RSI: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->rsi, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_ESI: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->rsi, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_SI:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->rsi, &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_SIL: { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->rsi,  &val, triton::size::byte);  break; }
          case triton::arch::ID_REG_X86_RSP: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->rsp, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_ESP: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->rsp, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_SP:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->rsp, &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_SPL: { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->rsp,  &val, triton::size::byte);  break; }
          case triton::arch::ID_REG_X86_RBP: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->rbp, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_EBP: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->rbp, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_BP:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->rbp, &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_BPL: { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->rbp,  &val, triton::size::byte);  break; }

          case triton::arch::ID_REG_X86_RIP: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->rip, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_EIP: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->rip, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_IP:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->rip, &val, triton::size::word);  break; }

          case triton::arch::ID_REG_X86_EFLAGS: {
            triton::uint64 val = static_cast<triton::uint64>(value);
            std::memcpy((triton::uint64*)this->eflags, &val, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_CF: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 0)) : (flag & ~(1 << 0));
            std::memcpy((triton::uint64*)this->eflags, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_PF: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 2)) : (flag & ~(1 << 2));
            std::memcpy((triton::uint64*)this->eflags, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_AF: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 4)) : (flag & ~(1 << 4));
            std::memcpy((triton::uint64*)this->eflags, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_ZF: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 6)) : (flag & ~(1 << 6));
            std::memcpy((triton::uint64*)this->eflags, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_SF: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 7)) : (flag & ~(1 << 7));
            std::memcpy((triton::uint64*)this->eflags, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_TF: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 8)) : (flag & ~(1 << 8));
            std::memcpy((triton::uint64*)this->eflags, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_IF: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 9)) : (flag & ~(1 << 9));
            std::memcpy((triton::uint64*)this->eflags, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_DF: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 10)) : (flag & ~(1 << 10));
            std::memcpy((triton::uint64*)this->eflags, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_OF: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 11)) : (flag & ~(1 << 11));
            std::memcpy((triton::uint64*)this->eflags, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_NT: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 14)) : (flag & ~(1 << 14));
            std::memcpy((triton::uint64*)this->eflags, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_RF: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 16)) : (flag & ~(1 << 16));
            std::memcpy((triton::uint64*)this->eflags, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_VM: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 17)) : (flag & ~(1 << 17));
            std::memcpy((triton::uint64*)this->eflags, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_AC: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 18)) : (flag & ~(1 << 18));
            std::memcpy((triton::uint64*)this->eflags, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_VIF: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 19)) : (flag & ~(1 << 19));
            std::memcpy((triton::uint64*)this->eflags, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_VIP: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 20)) : (flag & ~(1 << 20));
            std::memcpy((triton::uint64*)this->eflags, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_ID:  {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->eflags, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 21)) : (flag & ~(1 << 21));
            std::memcpy((triton::uint64*)this->eflags, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_R8:   { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->r8,  &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_R8D:  { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->r8,  &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_R8W:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->r8,  &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_R8B:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->r8,   &val, triton::size::byte);  break; }
          case triton::arch::ID_REG_X86_R9:   { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->r9,  &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_R9D:  { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->r9,  &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_R9W:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->r9,  &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_R9B:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->r9,   &val, triton::size::byte);  break; }
          case triton::arch::ID_REG_X86_R10:  { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->r10, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_R10D: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->r10, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_R10W: { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->r10, &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_R10B: { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->r10,  &val, triton::size::byte);  break; }
          case triton::arch::ID_REG_X86_R11:  { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->r11, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_R11D: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->r11, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_R11W: { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->r11, &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_R11B: { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->r11,  &val, triton::size::byte);  break; }
          case triton::arch::ID_REG_X86_R12:  { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->r12, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_R12D: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->r12, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_R12W: { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->r12, &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_R12B: { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->r12,  &val, triton::size::byte);  break; }
          case triton::arch::ID_REG_X86_R13:  { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->r13, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_R13D: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->r13, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_R13W: { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->r13, &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_R13B: { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->r13,  &val, triton::size::byte);  break; }
          case triton::arch::ID_REG_X86_R14:  { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->r14, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_R14D: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->r14, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_R14W: { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->r14, &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_R14B: { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->r14,  &val, triton::size::byte);  break; }
          case triton::arch::ID_REG_X86_R15:  { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->r15, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_R15D: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->r15, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_R15W: { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->r15, &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_R15B: { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->r15,  &val, triton::size::byte);  break; }

          case triton::arch::ID_REG_X86_MM0: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->st0, &val, triton::size::qword);  break; }
          case triton::arch::ID_REG_X86_MM1: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->st1, &val, triton::size::qword);  break; }
          case triton::arch::ID_REG_X86_MM2: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->st2, &val, triton::size::qword);  break; }
          case triton::arch::ID_REG_X86_MM3: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->st3, &val, triton::size::qword);  break; }
          case triton::arch::ID_REG_X86_MM4: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->st4, &val, triton::size::qword);  break; }
          case triton::arch::ID_REG_X86_MM5: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->st5, &val, triton::size::qword);  break; }
          case triton::arch::ID_REG_X86_MM6: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->st6, &val, triton::size::qword);  break; }
          case triton::arch::ID_REG_X86_MM7: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->st7, &val, triton::size::qword);  break; }

          case triton::arch::ID_REG_X86_ST0: { triton::utils::fromUintToBuffer(triton::utils::cast<triton::uint80>(value), this->st0); break; }
          case triton::arch::ID_REG_X86_ST1: { triton::utils::fromUintToBuffer(triton::utils::cast<triton::uint80>(value), this->st1); break; }
          case triton::arch::ID_REG_X86_ST2: { triton::utils::fromUintToBuffer(triton::utils::cast<triton::uint80>(value), this->st2); break; }
          case triton::arch::ID_REG_X86_ST3: { triton::utils::fromUintToBuffer(triton::utils::cast<triton::uint80>(value), this->st3); break; }
          case triton::arch::ID_REG_X86_ST4: { triton::utils::fromUintToBuffer(triton::utils::cast<triton::uint80>(value), this->st4); break; }
          case triton::arch::ID_REG_X86_ST5: { triton::utils::fromUintToBuffer(triton::utils::cast<triton::uint80>(value), this->st5); break; }
          case triton::arch::ID_REG_X86_ST6: { triton::utils::fromUintToBuffer(triton::utils::cast<triton::uint80>(value), this->st6); break; }
          case triton::arch::ID_REG_X86_ST7: { triton::utils::fromUintToBuffer(triton::utils::cast<triton::uint80>(value), this->st7); break; }

          case triton::arch::ID_REG_X86_XMM0:  { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->zmm0);  break; }
          case triton::arch::ID_REG_X86_XMM1:  { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->zmm1);  break; }
          case triton::arch::ID_REG_X86_XMM2:  { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->zmm2);  break; }
          case triton::arch::ID_REG_X86_XMM3:  { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->zmm3);  break; }
          case triton::arch::ID_REG_X86_XMM4:  { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->zmm4);  break; }
          case triton::arch::ID_REG_X86_XMM5:  { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->zmm5);  break; }
          case triton::arch::ID_REG_X86_XMM6:  { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->zmm6);  break; }
          case triton::arch::ID_REG_X86_XMM7:  { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->zmm7);  break; }
          case triton::arch::ID_REG_X86_XMM8:  { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->zmm8);  break; }
          case triton::arch::ID_REG_X86_XMM9:  { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->zmm9);  break; }
          case triton::arch::ID_REG_X86_XMM10: { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->zmm10); break; }
          case triton::arch::ID_REG_X86_XMM11: { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->zmm11); break; }
          case triton::arch::ID_REG_X86_XMM12: { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->zmm12); break; }
          case triton::arch::ID_REG_X86_XMM13: { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->zmm13); break; }
          case triton::arch::ID_REG_X86_XMM14: { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->zmm14); break; }
          case triton::arch::ID_REG_X86_XMM15: { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->zmm15); break; }

          case triton::arch::ID_REG_X86_YMM0:  { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->zmm0);  break; }
          case triton::arch::ID_REG_X86_YMM1:  { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->zmm1);  break; }
          case triton::arch::ID_REG_X86_YMM2:  { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->zmm2);  break; }
          case triton::arch::ID_REG_X86_YMM3:  { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->zmm3);  break; }
          case triton::arch::ID_REG_X86_YMM4:  { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->zmm4);  break; }
          case triton::arch::ID_REG_X86_YMM5:  { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->zmm5);  break; }
          case triton::arch::ID_REG_X86_YMM6:  { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->zmm6);  break; }
          case triton::arch::ID_REG_X86_YMM7:  { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->zmm7);  break; }
          case triton::arch::ID_REG_X86_YMM8:  { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->zmm8);  break; }
          case triton::arch::ID_REG_X86_YMM9:  { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->zmm9);  break; }
          case triton::arch::ID_REG_X86_YMM10: { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->zmm10); break; }
          case triton::arch::ID_REG_X86_YMM11: { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->zmm11); break; }
          case triton::arch::ID_REG_X86_YMM12: { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->zmm12); break; }
          case triton::arch::ID_REG_X86_YMM13: { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->zmm13); break; }
          case triton::arch::ID_REG_X86_YMM14: { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->zmm14); break; }
          case triton::arch::ID_REG_X86_YMM15: { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->zmm15); break; }

          case triton::arch::ID_REG_X86_ZMM0:  { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm0);  break; }
          case triton::arch::ID_REG_X86_ZMM1:  { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm1);  break; }
          case triton::arch::ID_REG_X86_ZMM2:  { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm2);  break; }
          case triton::arch::ID_REG_X86_ZMM3:  { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm3);  break; }
          case triton::arch::ID_REG_X86_ZMM4:  { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm4);  break; }
          case triton::arch::ID_REG_X86_ZMM5:  { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm5);  break; }
          case triton::arch::ID_REG_X86_ZMM6:  { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm6);  break; }
          case triton::arch::ID_REG_X86_ZMM7:  { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm7);  break; }
          case triton::arch::ID_REG_X86_ZMM8:  { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm8);  break; }
          case triton::arch::ID_REG_X86_ZMM9:  { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm9);  break; }
          case triton::arch::ID_REG_X86_ZMM10: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm10); break; }
          case triton::arch::ID_REG_X86_ZMM11: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm11); break; }
          case triton::arch::ID_REG_X86_ZMM12: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm12); break; }
          case triton::arch::ID_REG_X86_ZMM13: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm13); break; }
          case triton::arch::ID_REG_X86_ZMM14: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm14); break; }
          case triton::arch::ID_REG_X86_ZMM15: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm15); break; }
          case triton::arch::ID_REG_X86_ZMM16: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm16); break; }
          case triton::arch::ID_REG_X86_ZMM17: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm17); break; }
          case triton::arch::ID_REG_X86_ZMM18: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm18); break; }
          case triton::arch::ID_REG_X86_ZMM19: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm19); break; }
          case triton::arch::ID_REG_X86_ZMM20: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm20); break; }
          case triton::arch::ID_REG_X86_ZMM21: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm21); break; }
          case triton::arch::ID_REG_X86_ZMM22: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm22); break; }
          case triton::arch::ID_REG_X86_ZMM23: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm23); break; }
          case triton::arch::ID_REG_X86_ZMM24: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm24); break; }
          case triton::arch::ID_REG_X86_ZMM25: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm25); break; }
          case triton::arch::ID_REG_X86_ZMM26: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm26); break; }
          case triton::arch::ID_REG_X86_ZMM27: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm27); break; }
          case triton::arch::ID_REG_X86_ZMM28: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm28); break; }
          case triton::arch::ID_REG_X86_ZMM29: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm29); break; }
          case triton::arch::ID_REG_X86_ZMM30: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm30); break; }
          case triton::arch::ID_REG_X86_ZMM31: { triton::utils::fromUintToBuffer(static_cast<triton::uint512>(value), this->zmm31); break; }

          case triton::arch::ID_REG_X86_MXCSR: {
            triton::uint32 val = static_cast<triton::uint32>(value);
            std::memcpy((triton::uint32*)this->mxcsr, &val, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_MXCSR_MASK: {
            triton::uint32 val = static_cast<triton::uint32>(value);
            std::memcpy((triton::uint32*)this->mxcsr_mask, &val, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SSE_IE:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 0)) : (flag & ~(1 << 0));
            std::memcpy((triton::uint32*)this->mxcsr, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SSE_DE:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 1)) : (flag & ~(1 << 1));
            std::memcpy((triton::uint32*)this->mxcsr, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SSE_ZE:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 2)) : (flag & ~(1 << 2));
            std::memcpy((triton::uint32*)this->mxcsr, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SSE_OE:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 3)) : (flag & ~(1 << 3));
            std::memcpy((triton::uint32*)this->mxcsr, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SSE_UE:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 4)) : (flag & ~(1 << 4));
            std::memcpy((triton::uint32*)this->mxcsr, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SSE_PE:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 5)) : (flag & ~(1 << 5));
            std::memcpy((triton::uint32*)this->mxcsr, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SSE_DAZ: {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 6)) : (flag & ~(1 << 6));
            std::memcpy((triton::uint32*)this->mxcsr, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SSE_IM:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 7)) : (flag & ~(1 << 7));
            std::memcpy((triton::uint32*)this->mxcsr, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SSE_DM:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 8)) : (flag & ~(1 << 8));
            std::memcpy((triton::uint32*)this->mxcsr, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SSE_ZM:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 9)) : (flag & ~(1 << 9));
            std::memcpy((triton::uint32*)this->mxcsr, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SSE_OM:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 10)) : (flag & ~(1 << 10));
            std::memcpy((triton::uint32*)this->mxcsr, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SSE_UM:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 11)) : (flag & ~(1 << 11));
            std::memcpy((triton::uint32*)this->mxcsr, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SSE_PM:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 12)) : (flag & ~(1 << 12));
            std::memcpy((triton::uint32*)this->mxcsr, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SSE_RL:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 13)) : (flag & ~(1 << 13));
            std::memcpy((triton::uint32*)this->mxcsr, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SSE_RH:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 14)) : (flag & ~(1 << 14));
            std::memcpy((triton::uint32*)this->mxcsr, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SSE_FZ:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->mxcsr, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 15)) : (flag & ~(1 << 15));
            std::memcpy((triton::uint32*)this->mxcsr, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_FIP: {
            triton::uint64 val = static_cast<triton::uint64>(value);
            std::memcpy((triton::uint64*)this->fip, &val, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_FDP: {
            triton::uint64 val = static_cast<triton::uint64>(value);
            std::memcpy((triton::uint64*)this->fdp, &val, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_FCW: {
            triton::uint16 val = static_cast<triton::uint16>(value);
            std::memcpy((triton::uint16*)this->fcw, &val, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FSW: {
            triton::uint16 val = static_cast<triton::uint16>(value);
            std::memcpy((triton::uint16*)this->fsw, &val, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FOP: {
            triton::uint16 val = static_cast<triton::uint16>(value);
            std::memcpy((triton::uint16*)this->fop, &val, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCS: {
            triton::uint16 val = static_cast<triton::uint16>(value);
            std::memcpy((triton::uint16*)this->fcs, &val, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FDS: {
            triton::uint16 val = static_cast<triton::uint16>(value);
            std::memcpy((triton::uint16*)this->fds, &val, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FTW: {
            triton::uint16 val = static_cast<triton::uint16>(value);
            std::memcpy((triton::uint16*)this->ftw, &val, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_IM: {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 0)) : (flag & ~(1 << 0));
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_DM: {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 1)) : (flag & ~(1 << 1));
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_ZM: {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 2)) : (flag & ~(1 << 2));
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_OM: {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 3)) : (flag & ~(1 << 3));
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_UM: {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 4)) : (flag & ~(1 << 4));
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_PM: {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 5)) : (flag & ~(1 << 5));
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_PC: {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = (flag & 0xFCFF) | (static_cast<triton::uint16>(value) << 8);
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_RC: {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = (flag & 0xF3FF) | (static_cast<triton::uint16>(value) << 10);
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_X:  {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 12)) : (flag & ~(1 << 12));
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FSW_IE:  {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 0)) : (flag & ~(1 << 0));
            std::memcpy((triton::uint16*)this->fsw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FSW_DE:  {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 1)) : (flag & ~(1 << 1));
            std::memcpy((triton::uint16*)this->fsw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FSW_ZE:  {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 2)) : (flag & ~(1 << 2));
            std::memcpy((triton::uint16*)this->fsw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FSW_OE:  {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 3)) : (flag & ~(1 << 3));
            std::memcpy((triton::uint16*)this->fsw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FSW_UE:  {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 4)) : (flag & ~(1 << 4));
            std::memcpy((triton::uint16*)this->fsw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FSW_PE:  {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 5)) : (flag & ~(1 << 5));
            std::memcpy((triton::uint16*)this->fsw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FSW_SF:  {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 6)) : (flag & ~(1 << 6));
            std::memcpy((triton::uint16*)this->fsw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FSW_ES:  {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 7)) : (flag & ~(1 << 7));
            std::memcpy((triton::uint16*)this->fsw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FSW_C0:  {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 8)) : (flag & ~(1 << 8));
            std::memcpy((triton::uint16*)this->fsw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FSW_C1:  {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 9)) : (flag & ~(1 << 9));
            std::memcpy((triton::uint16*)this->fsw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FSW_C2:  {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 10)) : (flag & ~(1 << 10));
            std::memcpy((triton::uint16*)this->fsw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FSW_TOP: {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16));
            flag = (flag & 0xC7FF) | (static_cast<triton::uint16>(value) << 11);
            std::memcpy((triton::uint16*)this->fsw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FSW_C3:  {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 14)) : (flag & ~(1 << 14));
            std::memcpy((triton::uint16*)this->fsw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FSW_B:   {
            triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fsw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 15)) : (flag & ~(1 << 15));
            std::memcpy((triton::uint16*)this->fsw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_EFER: {
            triton::uint64 val = static_cast<triton::uint64>(value);
            std::memcpy((triton::uint64*)this->efer, &val, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_EFER_SCE:   {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 0)) : (flag & ~(1 << 0));
            std::memcpy((triton::uint64*)this->efer, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_EFER_LME:   {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 8)) : (flag & ~(1 << 8));
            std::memcpy((triton::uint64*)this->efer, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_EFER_LMA:   {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 10)) : (flag & ~(1 << 10));
            std::memcpy((triton::uint64*)this->efer, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_EFER_NXE:   {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 11)) : (flag & ~(1 << 11));
            std::memcpy((triton::uint64*)this->efer, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_EFER_SVME:  {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 12)) : (flag & ~(1 << 12));
            std::memcpy((triton::uint64*)this->efer, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_EFER_LMSLE: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 13)) : (flag & ~(1 << 13));
            std::memcpy((triton::uint64*)this->efer, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_EFER_FFXSR: {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 14)) : (flag & ~(1 << 14));
            std::memcpy((triton::uint64*)this->efer, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_EFER_TCE:   {
            triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 15)) : (flag & ~(1 << 15));
            std::memcpy((triton::uint64*)this->efer, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_CR0:  { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cr0,  &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_CR1:  { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cr1,  &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_CR2:  { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cr2,  &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_CR3:  { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cr3,  &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_CR4:  { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cr4,  &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_CR5:  { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cr5,  &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_CR6:  { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cr6,  &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_CR7:  { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cr7,  &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_CR8:  { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cr8,  &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_CR9:  { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cr9,  &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_CR10: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cr10, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_CR11: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cr11, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_CR12: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cr12, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_CR13: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cr13, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_CR14: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cr14, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_CR15: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cr15, &val, triton::size::qword); break; }

          case triton::arch::ID_REG_X86_DR0: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->dr0, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_DR1: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->dr1, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_DR2: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->dr2, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_DR3: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->dr3, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_DR6: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->dr6, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_DR7: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->dr7, &val, triton::size::qword); break; }

          case triton::arch::ID_REG_X86_CS: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->cs, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_DS: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->ds, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_ES: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->es, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_FS: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->fs, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_GS: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->gs, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_SS: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->ss, &val, triton::size::qword); break; }

          case triton::arch::ID_REG_X86_TSC: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->tsc, &val, triton::size::qword); break; }

          default:
            throw triton::exceptions::Cpu("x8664Cpu:setConcreteRegisterValue(): Invalid register.");
        }
      }


      bool x8664Cpu::isThumb(void) const {
        /* There is no thumb mode in x86_64 */
        return false;
      }


      void x8664Cpu::setThumb(bool state) {
        /* There is no thumb mode in x86_64 */
      }


      bool x8664Cpu::isMemoryExclusive(const triton::arch::MemoryAccess& mem) const {
        /* There is no exclusive memory access support in x86_64 */
        return false;
      }


      void x8664Cpu::setMemoryExclusiveTag(const triton::arch::MemoryAccess& mem, bool tag) {
        /* There is no exclusive memory access support in x86_64 */
      }


      bool x8664Cpu::isConcreteMemoryValueDefined(const triton::arch::MemoryAccess& mem) const {
        return this->isConcreteMemoryValueDefined(mem.getAddress(), mem.getSize());
      }


      bool x8664Cpu::isConcreteMemoryValueDefined(triton::uint64 baseAddr, triton::usize size) const {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) == this->memory.end()) {
            return false;
          }
        }
        return true;
      }


      void x8664Cpu::clearConcreteMemoryValue(const triton::arch::MemoryAccess& mem) {
        this->clearConcreteMemoryValue(mem.getAddress(), mem.getSize());
      }


      void x8664Cpu::clearConcreteMemoryValue(triton::uint64 baseAddr, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) != this->memory.end()) {
            this->memory.erase(baseAddr + index);
          }
        }
      }

    }; /* x86 namespace */
  }; /* arch namespace */
}; /* triton namespace */
