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
#include <triton/x86Cpu.hpp>



namespace triton {
  namespace arch {
    namespace x86 {

      x86Cpu::x86Cpu(triton::callbacks::Callbacks* callbacks) : x86Specifications(ARCH_X86) {
        this->callbacks = callbacks;
        this->handle    = 0;

        this->clear();
        this->disassInit();
      }


      x86Cpu::x86Cpu(const x86Cpu& other) : x86Specifications(ARCH_X86) {
        this->copy(other);
      }


      x86Cpu::~x86Cpu() {
        this->memory.clear();
        if (this->handle) {
          triton::extlibs::capstone::cs_close(&this->handle);
        }
      }


      void x86Cpu::disassInit(void) {
        if (this->handle) {
          triton::extlibs::capstone::cs_close(&this->handle);
        }

        if (triton::extlibs::capstone::cs_open(triton::extlibs::capstone::CS_ARCH_X86, triton::extlibs::capstone::CS_MODE_32, &this->handle) != triton::extlibs::capstone::CS_ERR_OK)
          throw triton::exceptions::Disassembly("x86Cpu::disassInit(): Cannot open capstone.");

        triton::extlibs::capstone::cs_option(this->handle, triton::extlibs::capstone::CS_OPT_DETAIL, triton::extlibs::capstone::CS_OPT_ON);
        triton::extlibs::capstone::cs_option(this->handle, triton::extlibs::capstone::CS_OPT_SYNTAX, triton::extlibs::capstone::CS_OPT_SYNTAX_INTEL);
      }


      void x86Cpu::copy(const x86Cpu& other) {
        this->callbacks = other.callbacks;
        this->memory    = other.memory;

        std::memcpy(this->eax,        other.eax,        sizeof(this->eax));
        std::memcpy(this->ebx,        other.ebx,        sizeof(this->ebx));
        std::memcpy(this->ecx,        other.ecx,        sizeof(this->ecx));
        std::memcpy(this->edx,        other.edx,        sizeof(this->edx));
        std::memcpy(this->edi,        other.edi,        sizeof(this->edi));
        std::memcpy(this->esi,        other.esi,        sizeof(this->esi));
        std::memcpy(this->esp,        other.esp,        sizeof(this->esp));
        std::memcpy(this->ebp,        other.ebp,        sizeof(this->ebp));
        std::memcpy(this->eip,        other.eip,        sizeof(this->eip));
        std::memcpy(this->eflags,     other.eflags,     sizeof(this->eflags));
        std::memcpy(this->st0,        other.st0,        sizeof(this->st0));
        std::memcpy(this->st1,        other.st1,        sizeof(this->st1));
        std::memcpy(this->st2,        other.st2,        sizeof(this->st2));
        std::memcpy(this->st3,        other.st3,        sizeof(this->st3));
        std::memcpy(this->st4,        other.st4,        sizeof(this->st4));
        std::memcpy(this->st5,        other.st5,        sizeof(this->st5));
        std::memcpy(this->st6,        other.st6,        sizeof(this->st6));
        std::memcpy(this->st7,        other.st7,        sizeof(this->st7));
        std::memcpy(this->ymm0,       other.ymm0,       sizeof(this->ymm0));
        std::memcpy(this->ymm1,       other.ymm1,       sizeof(this->ymm1));
        std::memcpy(this->ymm2,       other.ymm2,       sizeof(this->ymm2));
        std::memcpy(this->ymm3,       other.ymm3,       sizeof(this->ymm3));
        std::memcpy(this->ymm4,       other.ymm4,       sizeof(this->ymm4));
        std::memcpy(this->ymm5,       other.ymm5,       sizeof(this->ymm5));
        std::memcpy(this->ymm6,       other.ymm6,       sizeof(this->ymm6));
        std::memcpy(this->ymm7,       other.ymm7,       sizeof(this->ymm7));
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


      void x86Cpu::clear(void) {
        /* Clear memory */
        this->memory.clear();

        /* Clear registers */
        std::memset(this->eax,        0x00, sizeof(this->eax));
        std::memset(this->ebx,        0x00, sizeof(this->ebx));
        std::memset(this->ecx,        0x00, sizeof(this->ecx));
        std::memset(this->edx,        0x00, sizeof(this->edx));
        std::memset(this->edi,        0x00, sizeof(this->edi));
        std::memset(this->esi,        0x00, sizeof(this->esi));
        std::memset(this->esp,        0x00, sizeof(this->esp));
        std::memset(this->ebp,        0x00, sizeof(this->ebp));
        std::memset(this->eip,        0x00, sizeof(this->eip));
        std::memset(this->eflags,     0x00, sizeof(this->eflags));
        std::memset(this->st0,        0x00, sizeof(this->st0));
        std::memset(this->st1,        0x00, sizeof(this->st1));
        std::memset(this->st2,        0x00, sizeof(this->st2));
        std::memset(this->st3,        0x00, sizeof(this->st3));
        std::memset(this->st4,        0x00, sizeof(this->st4));
        std::memset(this->st5,        0x00, sizeof(this->st5));
        std::memset(this->st6,        0x00, sizeof(this->st6));
        std::memset(this->st7,        0x00, sizeof(this->st7));
        std::memset(this->ymm0,       0x00, sizeof(this->ymm0));
        std::memset(this->ymm1,       0x00, sizeof(this->ymm1));
        std::memset(this->ymm2,       0x00, sizeof(this->ymm2));
        std::memset(this->ymm3,       0x00, sizeof(this->ymm3));
        std::memset(this->ymm4,       0x00, sizeof(this->ymm4));
        std::memset(this->ymm5,       0x00, sizeof(this->ymm5));
        std::memset(this->ymm6,       0x00, sizeof(this->ymm6));
        std::memset(this->ymm7,       0x00, sizeof(this->ymm7));
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


      x86Cpu& x86Cpu::operator=(const x86Cpu& other) {
        this->copy(other);
        return *this;
      }


      triton::arch::endianness_e x86Cpu::getEndianness(void) const {
        return triton::arch::LE_ENDIANNESS;
      }


      bool x86Cpu::isFlag(triton::arch::register_e regId) const {
        if (regId >= triton::arch::ID_REG_X86_AC     && regId <= triton::arch::ID_REG_X86_ZF)     { return true; }
        if (regId >= triton::arch::ID_REG_X86_FTW    && regId <= triton::arch::ID_REG_X86_FDP)    { return true; }
        if (regId >= triton::arch::ID_REG_X86_SSE_IE && regId <= triton::arch::ID_REG_X86_SSE_FZ) { return true; }
        if (regId >= triton::arch::ID_REG_X86_FCW_IM && regId <= triton::arch::ID_REG_X86_FCW_X)  { return true; }
        if (regId >= triton::arch::ID_REG_X86_FSW_IE && regId <= triton::arch::ID_REG_X86_FSW_B)  { return true; }
        return false;
      }


      bool x86Cpu::isRegister(triton::arch::register_e regId) const {
        return (
          this->isGPR(regId)      ||
          this->isMMX(regId)      ||
          this->isSTX(regId)      ||
          this->isSSE(regId)      ||
          this->isFPU(regId)      ||
          this->isEFER(regId)     ||
          this->isTSC(regId)      ||
          this->isAVX256(regId)   ||
          this->isControl(regId)  ||
          this->isDebug(regId)    ||
          this->isSegment(regId)
        );
      }


      bool x86Cpu::isRegisterValid(triton::arch::register_e regId) const {
        return (this->isFlag(regId) || this->isRegister(regId));
      }


      bool x86Cpu::isGPR(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_EAX && regId <= triton::arch::ID_REG_X86_EFLAGS) ? true : false);
      }


      bool x86Cpu::isMMX(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_MM0 && regId <= triton::arch::ID_REG_X86_MM7) ? true : false);
      }


      bool x86Cpu::isSTX(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_ST0 && regId <= triton::arch::ID_REG_X86_ST7) ? true : false);
      }


      bool x86Cpu::isSSE(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_MXCSR && regId <= triton::arch::ID_REG_X86_XMM7) ? true : false);
      }


      bool x86Cpu::isFPU(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_FTW && regId <= triton::arch::ID_REG_X86_FDP) ? true : false);
      }


      bool x86Cpu::isEFER(triton::arch::register_e regId) const {
        return ((regId == triton::arch::ID_REG_X86_EFER) ? true : false);
      }


      bool x86Cpu::isTSC(triton::arch::register_e regId) const {
        return ((regId == triton::arch::ID_REG_X86_TSC) ? true : false);
      }


      bool x86Cpu::isAVX256(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_YMM0 && regId <= triton::arch::ID_REG_X86_YMM7) ? true : false);
      }


      bool x86Cpu::isControl(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_CR0 && regId <= triton::arch::ID_REG_X86_CR15) ? true : false);
      }


      bool x86Cpu::isDebug(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_DR0 && regId <= triton::arch::ID_REG_X86_DR7) ? true : false);
      }


      bool x86Cpu::isSegment(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_CS && regId <= triton::arch::ID_REG_X86_SS) ? true : false);
      }


      triton::uint32 x86Cpu::numberOfRegisters(void) const {
        return triton::arch::ID_REG_LAST_ITEM;
      }


      triton::uint32 x86Cpu::gprSize(void) const {
        return triton::size::dword;
      }


      triton::uint32 x86Cpu::gprBitSize(void) const {
        return triton::bitsize::dword;
      }



      const std::unordered_map<triton::arch::register_e, const triton::arch::Register>& x86Cpu::getAllRegisters(void) const {
        return this->id2reg;
      }

      const std::unordered_map<triton::uint64, triton::uint8, IdentityHash<triton::uint64>>& x86Cpu::getConcreteMemory(void) const {
        return this->memory;
      }


      std::set<const triton::arch::Register*> x86Cpu::getParentRegisters(void) const {
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


      const triton::arch::Register& x86Cpu::getRegister(triton::arch::register_e id) const {
        try {
          return this->id2reg.at(id);
        } catch (const std::out_of_range&) {
          throw triton::exceptions::Cpu("x86Cpu::getRegister(): Invalid register for this architecture.");
        }
      }


      const triton::arch::Register& x86Cpu::getRegister(const std::string& name) const {
        std::string lower = name;
        std::transform(lower.begin(), lower.end(), lower.begin(), [](unsigned char c){ return std::tolower(c); });
        try {
          return this->getRegister(this->name2id.at(lower));
        } catch (const std::out_of_range&) {
          throw triton::exceptions::Cpu("x86Cpu::getRegister(): Invalid register for this architecture.");
        }
      }


      const triton::arch::Register& x86Cpu::getParentRegister(const triton::arch::Register& reg) const {
        return this->getRegister(reg.getParent());
      }


      const triton::arch::Register& x86Cpu::getParentRegister(triton::arch::register_e id) const {
        return this->getParentRegister(this->getRegister(id));
      }


      const triton::arch::Register& x86Cpu::getProgramCounter(void) const {
        return this->getRegister(this->pcId);
      }


      const triton::arch::Register& x86Cpu::getStackPointer(void) const {
        return this->getRegister(this->spId);
      }


      void x86Cpu::disassembly(triton::arch::Instruction& inst) {
        triton::extlibs::capstone::cs_insn* insn;
        triton::usize count = 0;

        /* Check if the opcode and opcode' size are defined */
        if (inst.getOpcode() == nullptr || inst.getSize() == 0)
          throw triton::exceptions::Disassembly("x86Cpu::disassembly(): Opcode and opcodeSize must be definied.");

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
          inst.setArchitecture(triton::arch::ARCH_X86);

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
                break;
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
          triton::extlibs::capstone::cs_free(insn, count);
        }
        else
          throw triton::exceptions::Disassembly("x86Cpu::disassembly(): Failed to disassemble the given code.");
      }


      triton::uint8 x86Cpu::getConcreteMemoryValue(triton::uint64 addr, bool execCallbacks) const {
        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, triton::size::byte));

        auto it = this->memory.find(addr);
        if (it == this->memory.end()) {
          return 0x00;
        }

        return it->second;
      }


      triton::uint512 x86Cpu::getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks) const {
        triton::uint512 ret = 0;
        triton::uint64 addr = 0;
        triton::uint32 size = 0;

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, mem);

        addr = mem.getAddress();
        size = mem.getSize();

        if (size == 0 || size > triton::size::dqqword)
          throw triton::exceptions::Cpu("x86Cpu::getConcreteMemoryValue(): Invalid size memory.");

        for (triton::sint32 i = size-1; i >= 0; i--)
          ret = ((ret << triton::bitsize::byte) | this->getConcreteMemoryValue(addr+i, false));

        return ret;
      }


      std::vector<triton::uint8> x86Cpu::getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks) const {
        std::vector<triton::uint8> area;

        for (triton::usize index = 0; index < size; index++)
          area.push_back(this->getConcreteMemoryValue(baseAddr+index, execCallbacks));

        return area;
      }


      triton::uint512 x86Cpu::getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks) const {
        triton::uint512 value = 0;

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_REGISTER_VALUE, reg);

        switch (reg.getId()) {

          case triton::arch::ID_REG_X86_EAX: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->eax,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_AX:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->eax,  triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_AH:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->eax+1, triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_AL:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->eax,   triton::size::byte);  return val; }

          case triton::arch::ID_REG_X86_EBX: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->ebx,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_BX:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->ebx,  triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_BH:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->ebx+1, triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_BL:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->ebx,   triton::size::byte);  return val; }

          case triton::arch::ID_REG_X86_ECX: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->ecx,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CX:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->ecx,  triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_CH:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->ecx+1, triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_CL:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->ecx,   triton::size::byte);  return val; }

          case triton::arch::ID_REG_X86_EDX: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->edx,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_DX:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->edx,  triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_DH:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->edx+1, triton::size::byte);  return val; }
          case triton::arch::ID_REG_X86_DL:  { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->edx,   triton::size::byte);  return val; }

          case triton::arch::ID_REG_X86_EDI: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->edi, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_DI:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->edi, triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_DIL: { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->edi,  triton::size::byte);  return val; }

          case triton::arch::ID_REG_X86_ESI: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->esi, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_SI:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->esi, triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_SIL: { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->esi,  triton::size::byte);  return val; }

          case triton::arch::ID_REG_X86_ESP: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->esp, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_SP:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->esp, triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_SPL: { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->esp,  triton::size::byte);  return val; }

          case triton::arch::ID_REG_X86_EBP: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->ebp, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_BP:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->ebp, triton::size::word);  return val; }
          case triton::arch::ID_REG_X86_BPL: { triton::uint8  val = 0; std::memcpy(&val, (triton::uint8*)this->ebp,  triton::size::byte);  return val; }

          case triton::arch::ID_REG_X86_EIP: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->eip, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_IP:  { triton::uint16 val = 0; std::memcpy(&val, (triton::uint16*)this->eip, triton::size::word);  return val; }

          case triton::arch::ID_REG_X86_EFLAGS: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return val; }

          case triton::arch::ID_REG_X86_MM0: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->st0, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_MM1: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->st1, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_MM2: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->st2, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_MM3: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->st3, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_MM4: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->st4, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_MM5: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->st5, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_MM6: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->st6, triton::size::qword); return val; }
          case triton::arch::ID_REG_X86_MM7: { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->st7, triton::size::qword); return val; }

          case triton::arch::ID_REG_X86_ST2: { return triton::utils::cast<triton::uint512>(triton::utils::cast<triton::uint80>(this->st2)); }
          case triton::arch::ID_REG_X86_ST1: { return triton::utils::cast<triton::uint512>(triton::utils::cast<triton::uint80>(this->st1)); }
          case triton::arch::ID_REG_X86_ST3: { return triton::utils::cast<triton::uint512>(triton::utils::cast<triton::uint80>(this->st3)); }
          case triton::arch::ID_REG_X86_ST0: { return triton::utils::cast<triton::uint512>(triton::utils::cast<triton::uint80>(this->st0)); }
          case triton::arch::ID_REG_X86_ST4: { return triton::utils::cast<triton::uint512>(triton::utils::cast<triton::uint80>(this->st4)); }
          case triton::arch::ID_REG_X86_ST5: { return triton::utils::cast<triton::uint512>(triton::utils::cast<triton::uint80>(this->st5)); }
          case triton::arch::ID_REG_X86_ST6: { return triton::utils::cast<triton::uint512>(triton::utils::cast<triton::uint80>(this->st6)); }
          case triton::arch::ID_REG_X86_ST7: { return triton::utils::cast<triton::uint512>(triton::utils::cast<triton::uint80>(this->st7)); }

          case triton::arch::ID_REG_X86_XMM0: { return triton::utils::cast<triton::uint128>(this->ymm0); }
          case triton::arch::ID_REG_X86_XMM1: { return triton::utils::cast<triton::uint128>(this->ymm1); }
          case triton::arch::ID_REG_X86_XMM2: { return triton::utils::cast<triton::uint128>(this->ymm2); }
          case triton::arch::ID_REG_X86_XMM3: { return triton::utils::cast<triton::uint128>(this->ymm3); }
          case triton::arch::ID_REG_X86_XMM4: { return triton::utils::cast<triton::uint128>(this->ymm4); }
          case triton::arch::ID_REG_X86_XMM5: { return triton::utils::cast<triton::uint128>(this->ymm5); }
          case triton::arch::ID_REG_X86_XMM6: { return triton::utils::cast<triton::uint128>(this->ymm6); }
          case triton::arch::ID_REG_X86_XMM7: { return triton::utils::cast<triton::uint128>(this->ymm7); }

          case triton::arch::ID_REG_X86_YMM0: { return triton::utils::cast<triton::uint256>(this->ymm0); }
          case triton::arch::ID_REG_X86_YMM1: { return triton::utils::cast<triton::uint256>(this->ymm1); }
          case triton::arch::ID_REG_X86_YMM2: { return triton::utils::cast<triton::uint256>(this->ymm2); }
          case triton::arch::ID_REG_X86_YMM3: { return triton::utils::cast<triton::uint256>(this->ymm3); }
          case triton::arch::ID_REG_X86_YMM4: { return triton::utils::cast<triton::uint256>(this->ymm4); }
          case triton::arch::ID_REG_X86_YMM5: { return triton::utils::cast<triton::uint256>(this->ymm5); }
          case triton::arch::ID_REG_X86_YMM6: { return triton::utils::cast<triton::uint256>(this->ymm6); }
          case triton::arch::ID_REG_X86_YMM7: { return triton::utils::cast<triton::uint256>(this->ymm7); }


          case triton::arch::ID_REG_X86_TSC:        { triton::uint64 val = 0; std::memcpy(&val, (triton::uint64*)this->tsc,        sizeof(triton::uint64)); return val; }
          case triton::arch::ID_REG_X86_MXCSR:      { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->mxcsr,      sizeof(triton::uint32)); return val; }
          case triton::arch::ID_REG_X86_MXCSR_MASK: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->mxcsr_mask, sizeof(triton::uint32)); return val; }

          case triton::arch::ID_REG_X86_CR0:  { triton::uint32 val = 0; std::memcpy(&val, (triton::uint64*)this->cr0,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CR1:  { triton::uint32 val = 0; std::memcpy(&val, (triton::uint64*)this->cr1,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CR2:  { triton::uint32 val = 0; std::memcpy(&val, (triton::uint64*)this->cr2,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CR3:  { triton::uint32 val = 0; std::memcpy(&val, (triton::uint64*)this->cr3,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CR4:  { triton::uint32 val = 0; std::memcpy(&val, (triton::uint64*)this->cr4,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CR5:  { triton::uint32 val = 0; std::memcpy(&val, (triton::uint64*)this->cr5,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CR6:  { triton::uint32 val = 0; std::memcpy(&val, (triton::uint64*)this->cr6,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CR7:  { triton::uint32 val = 0; std::memcpy(&val, (triton::uint64*)this->cr7,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CR8:  { triton::uint32 val = 0; std::memcpy(&val, (triton::uint64*)this->cr8,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CR9:  { triton::uint32 val = 0; std::memcpy(&val, (triton::uint64*)this->cr9,  triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CR10: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint64*)this->cr10, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CR11: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint64*)this->cr11, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CR12: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint64*)this->cr12, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CR13: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint64*)this->cr13, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CR14: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint64*)this->cr14, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_CR15: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint64*)this->cr15, triton::size::dword); return val; }

          case triton::arch::ID_REG_X86_DR0: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->dr0, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_DR1: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->dr1, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_DR2: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->dr2, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_DR3: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->dr3, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_DR6: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->dr6, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_DR7: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->dr7, triton::size::dword); return val; }

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

          case triton::arch::ID_REG_X86_CF:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return ((flag >> 0) & 1);  }
          case triton::arch::ID_REG_X86_PF:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return ((flag >> 2) & 1);  }
          case triton::arch::ID_REG_X86_AF:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return ((flag >> 4) & 1);  }
          case triton::arch::ID_REG_X86_ZF:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return ((flag >> 6) & 1);  }
          case triton::arch::ID_REG_X86_SF:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return ((flag >> 7) & 1);  }
          case triton::arch::ID_REG_X86_TF:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return ((flag >> 8) & 1);  }
          case triton::arch::ID_REG_X86_IF:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return ((flag >> 9) & 1);  }
          case triton::arch::ID_REG_X86_DF:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return ((flag >> 10) & 1); }
          case triton::arch::ID_REG_X86_OF:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return ((flag >> 11) & 1); }
          case triton::arch::ID_REG_X86_NT:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return ((flag >> 14) & 1); }
          case triton::arch::ID_REG_X86_RF:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return ((flag >> 16) & 1); }
          case triton::arch::ID_REG_X86_VM:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return ((flag >> 17) & 1); }
          case triton::arch::ID_REG_X86_AC:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return ((flag >> 18) & 1); }
          case triton::arch::ID_REG_X86_VIF: { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return ((flag >> 19) & 1); }
          case triton::arch::ID_REG_X86_VIP: { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return ((flag >> 20) & 1); }
          case triton::arch::ID_REG_X86_ID:  { triton::uint32 flag = 0; std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32)); return ((flag >> 21) & 1); }

          case triton::arch::ID_REG_X86_CS: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->cs, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_DS: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->ds, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_ES: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->es, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_FS: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->fs, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_GS: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->gs, triton::size::dword); return val; }
          case triton::arch::ID_REG_X86_SS: { triton::uint32 val = 0; std::memcpy(&val, (triton::uint32*)this->ss, triton::size::dword); return val; }

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
            throw triton::exceptions::Cpu("x86Cpu::getConcreteRegisterValue(): Invalid register.");
        }

        return value;
      }


      void x86Cpu::setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value, bool execCallbacks) {
        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, triton::size::byte), value);
        this->memory[addr] = value;
      }


      void x86Cpu::setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value, bool execCallbacks) {
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();
        triton::uint512 cv  = value;

        if (cv > mem.getMaxValue())
          throw triton::exceptions::Register("x86Cpu::setConcreteMemoryValue(): You cannot set this concrete value (too big) to this memory access.");

        if (size == 0 || size > triton::size::dqqword)
          throw triton::exceptions::Cpu("x86Cpu::setConcreteMemoryValue(): Invalid size memory.");

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, mem, value);

        for (triton::uint32 i = 0; i < size; i++) {
          this->memory[addr+i] = static_cast<triton::uint8>(cv & 0xff);
          cv >>= 8;
        }
      }


      void x86Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values, bool execCallbacks) {
        this->memory.reserve(values.size() + this->memory.size());
        for (triton::usize index = 0; index < values.size(); index++) {
          this->setConcreteMemoryValue(baseAddr+index, values[index], execCallbacks);
        }
      }


      void x86Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const void* area, triton::usize size, bool execCallbacks) {
        this->memory.reserve(size + this->memory.size());
        for (triton::usize index = 0; index < size; index++) {
          this->setConcreteMemoryValue(baseAddr+index, reinterpret_cast<const triton::uint8*>(area)[index], execCallbacks);
        }
      }


      void x86Cpu::setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value, bool execCallbacks) {
        if (value > reg.getMaxValue())
          throw triton::exceptions::Register("x86Cpu::setConcreteRegisterValue(): You cannot set this concrete value (too big) to this register.");

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_REGISTER_VALUE, reg, value);

        switch (reg.getId()) {

          case triton::arch::ID_REG_X86_EAX: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->eax,    &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_AX:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->eax,    &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_AH:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)(this->eax+1), &val, triton::size::byte);  break; }
          case triton::arch::ID_REG_X86_AL:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->eax,     &val, triton::size::byte);  break; }

          case triton::arch::ID_REG_X86_EBX: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->ebx,    &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_BX:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->ebx,    &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_BH:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)(this->ebx+1), &val, triton::size::byte);  break; }
          case triton::arch::ID_REG_X86_BL:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->ebx,     &val, triton::size::byte);  break; }

          case triton::arch::ID_REG_X86_ECX: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->ecx,    &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_CX:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->ecx,    &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_CH:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)(this->ecx+1), &val, triton::size::byte);  break; }
          case triton::arch::ID_REG_X86_CL:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->ecx,     &val, triton::size::byte);  break; }

          case triton::arch::ID_REG_X86_EDX: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->edx,    &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_DX:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->edx,    &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_DH:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)(this->edx+1), &val, triton::size::byte);  break; }
          case triton::arch::ID_REG_X86_DL:  { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->edx,     &val, triton::size::byte);  break; }

          case triton::arch::ID_REG_X86_EDI: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->edi,    &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_DI:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->edi,    &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_DIL: { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->edi,     &val, triton::size::byte);  break; }

          case triton::arch::ID_REG_X86_ESI: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->esi,    &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_SI:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->esi,    &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_SIL: { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->esi,     &val, triton::size::byte);  break; }

          case triton::arch::ID_REG_X86_ESP: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->esp,    &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_SP:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->esp,    &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_SPL: { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->esp,     &val, triton::size::byte);  break; }

          case triton::arch::ID_REG_X86_EBP: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->ebp,    &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_BP:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->ebp,    &val, triton::size::word);  break; }
          case triton::arch::ID_REG_X86_BPL: { triton::uint8  val = static_cast<triton::uint8>(value);  std::memcpy((triton::uint8*)this->ebp,     &val, triton::size::byte);  break; }

          case triton::arch::ID_REG_X86_EIP: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->eip,    &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_IP:  { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->eip,    &val, triton::size::word);  break; }

          case triton::arch::ID_REG_X86_EFLAGS: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->eflags, &val, sizeof(triton::uint32)); break; }

          case triton::arch::ID_REG_X86_MM0: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->st0, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_MM1: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->st1, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_MM2: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->st2, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_MM3: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->st3, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_MM4: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->st4, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_MM5: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->st5, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_MM6: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->st6, &val, triton::size::qword); break; }
          case triton::arch::ID_REG_X86_MM7: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->st7, &val, triton::size::qword); break; }

          case triton::arch::ID_REG_X86_ST0: { triton::utils::fromUintToBuffer(triton::utils::cast<triton::uint80>(value), this->st0); break; }
          case triton::arch::ID_REG_X86_ST1: { triton::utils::fromUintToBuffer(triton::utils::cast<triton::uint80>(value), this->st1); break; }
          case triton::arch::ID_REG_X86_ST2: { triton::utils::fromUintToBuffer(triton::utils::cast<triton::uint80>(value), this->st2); break; }
          case triton::arch::ID_REG_X86_ST3: { triton::utils::fromUintToBuffer(triton::utils::cast<triton::uint80>(value), this->st3); break; }
          case triton::arch::ID_REG_X86_ST4: { triton::utils::fromUintToBuffer(triton::utils::cast<triton::uint80>(value), this->st4); break; }
          case triton::arch::ID_REG_X86_ST5: { triton::utils::fromUintToBuffer(triton::utils::cast<triton::uint80>(value), this->st5); break; }
          case triton::arch::ID_REG_X86_ST6: { triton::utils::fromUintToBuffer(triton::utils::cast<triton::uint80>(value), this->st6); break; }
          case triton::arch::ID_REG_X86_ST7: { triton::utils::fromUintToBuffer(triton::utils::cast<triton::uint80>(value), this->st7); break; }

          case triton::arch::ID_REG_X86_XMM0: { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->ymm0); break; }
          case triton::arch::ID_REG_X86_XMM1: { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->ymm1); break; }
          case triton::arch::ID_REG_X86_XMM2: { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->ymm2); break; }
          case triton::arch::ID_REG_X86_XMM3: { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->ymm3); break; }
          case triton::arch::ID_REG_X86_XMM4: { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->ymm4); break; }
          case triton::arch::ID_REG_X86_XMM5: { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->ymm5); break; }
          case triton::arch::ID_REG_X86_XMM6: { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->ymm6); break; }
          case triton::arch::ID_REG_X86_XMM7: { triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->ymm7); break; }

          case triton::arch::ID_REG_X86_YMM0: { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->ymm0); break; }
          case triton::arch::ID_REG_X86_YMM1: { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->ymm1); break; }
          case triton::arch::ID_REG_X86_YMM2: { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->ymm2); break; }
          case triton::arch::ID_REG_X86_YMM3: { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->ymm3); break; }
          case triton::arch::ID_REG_X86_YMM4: { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->ymm4); break; }
          case triton::arch::ID_REG_X86_YMM5: { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->ymm5); break; }
          case triton::arch::ID_REG_X86_YMM6: { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->ymm6); break; }
          case triton::arch::ID_REG_X86_YMM7: { triton::utils::fromUintToBuffer(static_cast<triton::uint256>(value), this->ymm7); break; }

          case triton::arch::ID_REG_X86_MXCSR:      { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->mxcsr,      &val, sizeof(triton::uint32)); break; }
          case triton::arch::ID_REG_X86_MXCSR_MASK: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->mxcsr_mask, &val, sizeof(triton::uint32)); break; }

          case triton::arch::ID_REG_X86_CR0:  { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cr0, &val, triton::size::dword);  break; }
          case triton::arch::ID_REG_X86_CR1:  { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cr1, &val, triton::size::dword);  break; }
          case triton::arch::ID_REG_X86_CR2:  { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cr2, &val, triton::size::dword);  break; }
          case triton::arch::ID_REG_X86_CR3:  { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cr3, &val, triton::size::dword);  break; }
          case triton::arch::ID_REG_X86_CR4:  { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cr4, &val, triton::size::dword);  break; }
          case triton::arch::ID_REG_X86_CR5:  { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cr5, &val, triton::size::dword);  break; }
          case triton::arch::ID_REG_X86_CR6:  { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cr6, &val, triton::size::dword);  break; }
          case triton::arch::ID_REG_X86_CR7:  { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cr7, &val, triton::size::dword);  break; }
          case triton::arch::ID_REG_X86_CR8:  { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cr8, &val, triton::size::dword);  break; }
          case triton::arch::ID_REG_X86_CR9:  { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cr9, &val, triton::size::dword);  break; }
          case triton::arch::ID_REG_X86_CR10: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cr10, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_CR11: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cr11, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_CR12: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cr12, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_CR13: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cr13, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_CR14: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cr14, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_CR15: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cr15, &val, triton::size::dword); break; }

          case triton::arch::ID_REG_X86_DR0: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->dr0, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_DR1: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->dr1, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_DR2: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->dr2, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_DR3: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->dr3, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_DR6: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->dr6, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_DR7: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->dr7, &val, triton::size::dword); break; }

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

          case triton::arch::ID_REG_X86_CF:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 0)) : (flag & ~(1 << 0));
            std::memcpy((triton::uint32*)this->eflags, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_PF:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 2)) : (flag & ~(1 << 2));
            std::memcpy((triton::uint32*)this->eflags, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_AF:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 4)) : (flag & ~(1 << 4));
            std::memcpy((triton::uint32*)this->eflags, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_ZF:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 6)) : (flag & ~(1 << 6));
            std::memcpy((triton::uint32*)this->eflags, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_SF:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 7)) : (flag & ~(1 << 7));
            std::memcpy((triton::uint32*)this->eflags, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_TF:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 8)) : (flag & ~(1 << 8));
            std::memcpy((triton::uint32*)this->eflags, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_IF:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 9)) : (flag & ~(1 << 9));
            std::memcpy((triton::uint32*)this->eflags, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_DF:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 10)) : (flag & ~(1 << 10));
            std::memcpy((triton::uint32*)this->eflags, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_OF:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 11)) : (flag & ~(1 << 11));
            std::memcpy((triton::uint32*)this->eflags, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_NT:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 14)) : (flag & ~(1 << 14));
            std::memcpy((triton::uint32*)this->eflags, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_RF:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 16)) : (flag & ~(1 << 16));
            std::memcpy((triton::uint32*)this->eflags, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_VM:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 17)) : (flag & ~(1 << 17));
            std::memcpy((triton::uint32*)this->eflags, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_AC:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 18)) : (flag & ~(1 << 18));
            std::memcpy((triton::uint32*)this->eflags, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_VIF: {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 19)) : (flag & ~(1 << 19));
            std::memcpy((triton::uint32*)this->eflags, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_VIP: {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 20)) : (flag & ~(1 << 20));
            std::memcpy((triton::uint32*)this->eflags, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_ID:  {
            triton::uint32 flag = 0;
            std::memcpy(&flag, (triton::uint32*)this->eflags, sizeof(triton::uint32));
            flag = !value.is_zero() ? (flag | (1 << 21)) : (flag & ~(1 << 21));
            std::memcpy((triton::uint32*)this->eflags, &flag, sizeof(triton::uint32));
            break;
          }

          case triton::arch::ID_REG_X86_CS: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->cs, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_DS: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->ds, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_ES: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->es, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_FS: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->fs, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_GS: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->gs, &val, triton::size::dword); break; }
          case triton::arch::ID_REG_X86_SS: { triton::uint32 val = static_cast<triton::uint32>(value); std::memcpy((triton::uint32*)this->ss, &val, triton::size::dword); break; }

          case triton::arch::ID_REG_X86_FIP: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->fip, &val, sizeof(triton::uint64)); break; }
          case triton::arch::ID_REG_X86_FDP: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->fdp, &val, sizeof(triton::uint64)); break; }
          case triton::arch::ID_REG_X86_FCW: { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->fcw, &val, sizeof(triton::uint16)); break; }
          case triton::arch::ID_REG_X86_FSW: { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->fsw, &val, sizeof(triton::uint16)); break; }
          case triton::arch::ID_REG_X86_FOP: { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->fop, &val, sizeof(triton::uint16)); break; }
          case triton::arch::ID_REG_X86_FCS: { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->fcs, &val, sizeof(triton::uint16)); break; }
          case triton::arch::ID_REG_X86_FDS: { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->fds, &val, sizeof(triton::uint16)); break; }
          case triton::arch::ID_REG_X86_FTW: { triton::uint16 val = static_cast<triton::uint16>(value); std::memcpy((triton::uint16*)this->ftw, &val, sizeof(triton::uint16)); break; }

          case triton::arch::ID_REG_X86_FCW_IM: { triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 0)) : (flag & ~(1 << 0));
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_DM: { triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 1)) : (flag & ~(1 << 1));
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_ZM: { triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 2)) : (flag & ~(1 << 2));
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_OM: { triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 3)) : (flag & ~(1 << 3));
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_UM: { triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 4)) : (flag & ~(1 << 4));
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_PM: { triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = !value.is_zero() ? (flag | (1 << 5)) : (flag & ~(1 << 5));
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_PC: { triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = (flag & 0xFCFF) | (static_cast<triton::uint16>(value) << 8);
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_RC: { triton::uint16 flag = 0;
            std::memcpy(&flag, (triton::uint16*)this->fcw, sizeof(triton::uint16));
            flag = (flag & 0xF3FF) | (static_cast<triton::uint16>(value) << 10);
            std::memcpy((triton::uint16*)this->fcw, &flag, sizeof(triton::uint16));
            break;
          }

          case triton::arch::ID_REG_X86_FCW_X:  { triton::uint16 flag = 0;
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

          case triton::arch::ID_REG_X86_EFER_SCE:   { triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 0)) : (flag & ~(1 << 0));
            std::memcpy((triton::uint64*)this->efer, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_EFER_LME:   { triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 8)) : (flag & ~(1 << 8));
            std::memcpy((triton::uint64*)this->efer, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_EFER_LMA:   { triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 10)) : (flag & ~(1 << 10));
            std::memcpy((triton::uint64*)this->efer, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_EFER_NXE:   { triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 11)) : (flag & ~(1 << 11));
            std::memcpy((triton::uint64*)this->efer, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_EFER_SVME:  { triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 12)) : (flag & ~(1 << 12));
            std::memcpy((triton::uint64*)this->efer, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_EFER_LMSLE: { triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 13)) : (flag & ~(1 << 13));
            std::memcpy((triton::uint64*)this->efer, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_EFER_FFXSR: { triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 14)) : (flag & ~(1 << 14));
            std::memcpy((triton::uint64*)this->efer, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_EFER_TCE:   { triton::uint64 flag = 0;
            std::memcpy(&flag, (triton::uint64*)this->efer, sizeof(triton::uint64));
            flag = !value.is_zero() ? (flag | (1 << 15)) : (flag & ~(1 << 15));
            std::memcpy((triton::uint64*)this->efer, &flag, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_EFER: {
            triton::uint64 val = static_cast<triton::uint64>(value);
            std::memcpy((triton::uint64*)this->efer, &val, sizeof(triton::uint64));
            break;
          }

          case triton::arch::ID_REG_X86_TSC: { triton::uint64 val = static_cast<triton::uint64>(value); std::memcpy((triton::uint64*)this->tsc, &val, triton::size::qword); break; }

          default:
            throw triton::exceptions::Cpu("x86Cpu:setConcreteRegisterValue() - Invalid register.");
        }
      }


      bool x86Cpu::isThumb(void) const {
        /* There is no thumb mode in x86 */
        return false;
      }


      void x86Cpu::setThumb(bool state) {
        /* There is no thumb mode in x86 */
      }


      bool x86Cpu::isMemoryExclusive(const triton::arch::MemoryAccess& mem) const {
        /* There is no exclusive memory access support in x86 */
        return false;
      }


      void x86Cpu::setMemoryExclusiveTag(const triton::arch::MemoryAccess& mem, bool tag) {
        /* There is no exclusive memory access support in x86 */
      }


      bool x86Cpu::isConcreteMemoryValueDefined(const triton::arch::MemoryAccess& mem) const {
        return this->isConcreteMemoryValueDefined(mem.getAddress(), mem.getSize());
      }


      bool x86Cpu::isConcreteMemoryValueDefined(triton::uint64 baseAddr, triton::usize size) const {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) == this->memory.end()) {
            return false;
          }
        }
        return true;
      }


      void x86Cpu::clearConcreteMemoryValue(const triton::arch::MemoryAccess& mem) {
        this->clearConcreteMemoryValue(mem.getAddress(), mem.getSize());
      }


      void x86Cpu::clearConcreteMemoryValue(triton::uint64 baseAddr, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) != this->memory.end()) {
            this->memory.erase(baseAddr + index);
          }
        }
      }

    }; /* x86 namespace */
  }; /* arch namespace */
}; /* triton namespace */
