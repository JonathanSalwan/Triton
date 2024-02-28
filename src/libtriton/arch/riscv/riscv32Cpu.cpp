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
#include <triton/riscv32Cpu.hpp>



namespace triton {
  namespace arch {
    namespace riscv {

      riscv32Cpu::riscv32Cpu(triton::callbacks::Callbacks* callbacks) : riscvSpecifications(ARCH_RV32) {
        this->callbacks = callbacks;
        this->handle    = 0;

        this->clear();
        this->disassInit();
      }


      riscv32Cpu::riscv32Cpu(const riscv32Cpu& other) : riscvSpecifications(ARCH_RV32) {
        this->copy(other);
      }


      riscv32Cpu::~riscv32Cpu() {
        this->memory.clear();
        if (this->handle) {
          triton::extlibs::capstone::cs_close(&this->handle);
        }
      }

      void riscv32Cpu::disassInit(void) {
        if (this->handle) {
          triton::extlibs::capstone::cs_close(&this->handle);
        }

        // CS_MODE_RISCV32 | CS_MODE_RISCVC
        auto rv_mode = static_cast<triton::extlibs::capstone::cs_mode>((1 << 0) | (1 << 2));
        if (triton::extlibs::capstone::cs_open(triton::extlibs::capstone::CS_ARCH_RISCV, rv_mode, &this->handle) != triton::extlibs::capstone::CS_ERR_OK)
          throw triton::exceptions::Disassembly("riscv32Cpu::disassInit(): Cannot open capstone.");

        triton::extlibs::capstone::cs_option(this->handle, triton::extlibs::capstone::CS_OPT_DETAIL, triton::extlibs::capstone::CS_OPT_ON);
      }


      void riscv32Cpu::copy(const riscv32Cpu& other) {
        this->callbacks = other.callbacks;
        this->memory    = other.memory;

        std::memcpy(this->x0,   other.x0,   sizeof(this->x0));
        std::memcpy(this->x1,   other.x1,   sizeof(this->x1));
        std::memcpy(this->sp,   other.sp,   sizeof(this->sp));
        std::memcpy(this->x3,   other.x3,   sizeof(this->x3));
        std::memcpy(this->x4,   other.x4,   sizeof(this->x4));
        std::memcpy(this->x5,   other.x5,   sizeof(this->x5));
        std::memcpy(this->x6,   other.x6,   sizeof(this->x6));
        std::memcpy(this->x7,   other.x7,   sizeof(this->x7));
        std::memcpy(this->x8,   other.x8,   sizeof(this->x8));
        std::memcpy(this->x9,   other.x9,   sizeof(this->x9));
        std::memcpy(this->x10,  other.x10,  sizeof(this->x10));
        std::memcpy(this->x11,  other.x11,  sizeof(this->x11));
        std::memcpy(this->x12,  other.x12,  sizeof(this->x12));
        std::memcpy(this->x13,  other.x13,  sizeof(this->x13));
        std::memcpy(this->x14,  other.x14,  sizeof(this->x14));
        std::memcpy(this->x15,  other.x15,  sizeof(this->x15));
        std::memcpy(this->x16,  other.x16,  sizeof(this->x16));
        std::memcpy(this->x17,  other.x17,  sizeof(this->x17));
        std::memcpy(this->x18,  other.x18,  sizeof(this->x18));
        std::memcpy(this->x19,  other.x19,  sizeof(this->x19));
        std::memcpy(this->x20,  other.x20,  sizeof(this->x20));
        std::memcpy(this->x21,  other.x21,  sizeof(this->x21));
        std::memcpy(this->x22,  other.x22,  sizeof(this->x22));
        std::memcpy(this->x23,  other.x23,  sizeof(this->x23));
        std::memcpy(this->x24,  other.x24,  sizeof(this->x24));
        std::memcpy(this->x25,  other.x25,  sizeof(this->x25));
        std::memcpy(this->x26,  other.x26,  sizeof(this->x26));
        std::memcpy(this->x27,  other.x27,  sizeof(this->x27));
        std::memcpy(this->x28,  other.x28,  sizeof(this->x28));
        std::memcpy(this->x29,  other.x29,  sizeof(this->x29));
        std::memcpy(this->x30,  other.x30,  sizeof(this->x30));
        std::memcpy(this->x31,  other.x31,  sizeof(this->x31));
        std::memcpy(this->pc,   other.pc,   sizeof(this->pc));
        std::memcpy(this->f0,   other.f0,   sizeof(this->f0));
        std::memcpy(this->f1,   other.f1,   sizeof(this->f1));
        std::memcpy(this->f2,   other.f2,   sizeof(this->f2));
        std::memcpy(this->f3,   other.f3,   sizeof(this->f3));
        std::memcpy(this->f4,   other.f4,   sizeof(this->f4));
        std::memcpy(this->f5,   other.f5,   sizeof(this->f5));
        std::memcpy(this->f6,   other.f6,   sizeof(this->f6));
        std::memcpy(this->f7,   other.f7,   sizeof(this->f7));
        std::memcpy(this->f8,   other.f8,   sizeof(this->f8));
        std::memcpy(this->f9,   other.f9,   sizeof(this->f9));
        std::memcpy(this->f10,  other.f10,  sizeof(this->f10));
        std::memcpy(this->f11,  other.f11,  sizeof(this->f11));
        std::memcpy(this->f12,  other.f12,  sizeof(this->f12));
        std::memcpy(this->f13,  other.f13,  sizeof(this->f13));
        std::memcpy(this->f14,  other.f14,  sizeof(this->f14));
        std::memcpy(this->f15,  other.f15,  sizeof(this->f15));
        std::memcpy(this->f16,  other.f16,  sizeof(this->f16));
        std::memcpy(this->f17,  other.f17,  sizeof(this->f17));
        std::memcpy(this->f18,  other.f18,  sizeof(this->f18));
        std::memcpy(this->f19,  other.f19,  sizeof(this->f19));
        std::memcpy(this->f20,  other.f20,  sizeof(this->f20));
        std::memcpy(this->f21,  other.f21,  sizeof(this->f21));
        std::memcpy(this->f22,  other.f22,  sizeof(this->f22));
        std::memcpy(this->f23,  other.f23,  sizeof(this->f23));
        std::memcpy(this->f24,  other.f24,  sizeof(this->f24));
        std::memcpy(this->f25,  other.f25,  sizeof(this->f25));
        std::memcpy(this->f26,  other.f26,  sizeof(this->f26));
        std::memcpy(this->f27,  other.f27,  sizeof(this->f27));
        std::memcpy(this->f28,  other.f28,  sizeof(this->f28));
        std::memcpy(this->f29,  other.f29,  sizeof(this->f29));
        std::memcpy(this->f30,  other.f30,  sizeof(this->f30));
        std::memcpy(this->f31,  other.f31,  sizeof(this->f31));
      }


      void riscv32Cpu::clear(void) {
        /* Clear memory */
        this->memory.clear();

        /* Clear registers */
        std::memset(this->x0,   0x00,  sizeof(this->x0));
        std::memset(this->x1,   0x00,  sizeof(this->x1));
        std::memset(this->sp,   0x00,  sizeof(this->sp));
        std::memset(this->x3,   0x00,  sizeof(this->x3));
        std::memset(this->x4,   0x00,  sizeof(this->x4));
        std::memset(this->x5,   0x00,  sizeof(this->x5));
        std::memset(this->x6,   0x00,  sizeof(this->x6));
        std::memset(this->x7,   0x00,  sizeof(this->x7));
        std::memset(this->x8,   0x00,  sizeof(this->x8));
        std::memset(this->x9,   0x00,  sizeof(this->x9));
        std::memset(this->x10,  0x00,  sizeof(this->x10));
        std::memset(this->x11,  0x00,  sizeof(this->x11));
        std::memset(this->x12,  0x00,  sizeof(this->x12));
        std::memset(this->x13,  0x00,  sizeof(this->x13));
        std::memset(this->x14,  0x00,  sizeof(this->x14));
        std::memset(this->x15,  0x00,  sizeof(this->x15));
        std::memset(this->x16,  0x00,  sizeof(this->x16));
        std::memset(this->x17,  0x00,  sizeof(this->x17));
        std::memset(this->x18,  0x00,  sizeof(this->x18));
        std::memset(this->x19,  0x00,  sizeof(this->x19));
        std::memset(this->x20,  0x00,  sizeof(this->x20));
        std::memset(this->x21,  0x00,  sizeof(this->x21));
        std::memset(this->x22,  0x00,  sizeof(this->x22));
        std::memset(this->x23,  0x00,  sizeof(this->x23));
        std::memset(this->x24,  0x00,  sizeof(this->x24));
        std::memset(this->x25,  0x00,  sizeof(this->x25));
        std::memset(this->x26,  0x00,  sizeof(this->x26));
        std::memset(this->x27,  0x00,  sizeof(this->x27));
        std::memset(this->x28,  0x00,  sizeof(this->x28));
        std::memset(this->x29,  0x00,  sizeof(this->x29));
        std::memset(this->x30,  0x00,  sizeof(this->x30));
        std::memset(this->x31,  0x00,  sizeof(this->x31));
        std::memset(this->pc,   0x00,  sizeof(this->pc));
        std::memset(this->f0,   0x00,  sizeof(this->f0));
        std::memset(this->f1,   0x00,  sizeof(this->f1));
        std::memset(this->f2,   0x00,  sizeof(this->f2));
        std::memset(this->f3,   0x00,  sizeof(this->f3));
        std::memset(this->f4,   0x00,  sizeof(this->f4));
        std::memset(this->f5,   0x00,  sizeof(this->f5));
        std::memset(this->f6,   0x00,  sizeof(this->f6));
        std::memset(this->f7,   0x00,  sizeof(this->f7));
        std::memset(this->f8,   0x00,  sizeof(this->f8));
        std::memset(this->f9,   0x00,  sizeof(this->f9));
        std::memset(this->f10,  0x00,  sizeof(this->f10));
        std::memset(this->f11,  0x00,  sizeof(this->f11));
        std::memset(this->f12,  0x00,  sizeof(this->f12));
        std::memset(this->f13,  0x00,  sizeof(this->f13));
        std::memset(this->f14,  0x00,  sizeof(this->f14));
        std::memset(this->f15,  0x00,  sizeof(this->f15));
        std::memset(this->f16,  0x00,  sizeof(this->f16));
        std::memset(this->f17,  0x00,  sizeof(this->f17));
        std::memset(this->f18,  0x00,  sizeof(this->f18));
        std::memset(this->f19,  0x00,  sizeof(this->f19));
        std::memset(this->f20,  0x00,  sizeof(this->f20));
        std::memset(this->f21,  0x00,  sizeof(this->f21));
        std::memset(this->f22,  0x00,  sizeof(this->f22));
        std::memset(this->f23,  0x00,  sizeof(this->f23));
        std::memset(this->f24,  0x00,  sizeof(this->f24));
        std::memset(this->f25,  0x00,  sizeof(this->f25));
        std::memset(this->f26,  0x00,  sizeof(this->f26));
        std::memset(this->f27,  0x00,  sizeof(this->f27));
        std::memset(this->f28,  0x00,  sizeof(this->f28));
        std::memset(this->f29,  0x00,  sizeof(this->f29));
        std::memset(this->f30,  0x00,  sizeof(this->f30));
        std::memset(this->f31,  0x00,  sizeof(this->f31));
      }


      riscv32Cpu& riscv32Cpu::operator=(const riscv32Cpu& other) {
        this->copy(other);
        return *this;
      }


      triton::arch::endianness_e riscv32Cpu::getEndianness(void) const {
        return triton::arch::LE_ENDIANNESS;
      }


      bool riscv32Cpu::isRegister(triton::arch::register_e regId) const {
        return (this->isGPR(regId) || this->isFPU(regId) || regId == triton::arch::ID_REG_RV32_PC);
      }


      bool riscv32Cpu::isRegisterValid(triton::arch::register_e regId) const {
        return (this->isFlag(regId) || this->isRegister(regId));
      }


      bool riscv32Cpu::isGPR(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_RV32_X0 && regId <= triton::arch::ID_REG_RV32_X31) ? true : false);
      }


      bool riscv32Cpu::isFPU(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_RV32_F0 && regId <= triton::arch::ID_REG_RV32_F31) ? true : false);
      }


      bool riscv32Cpu::isFlag(triton::arch::register_e regId) const {
        return false;
      }


      triton::uint32 riscv32Cpu::numberOfRegisters(void) const {
        return triton::arch::ID_REG_LAST_ITEM;
      }


      triton::uint32 riscv32Cpu::gprSize(void) const {
        return triton::size::dword;
      }


      triton::uint32 riscv32Cpu::gprBitSize(void) const {
        return triton::bitsize::dword;
      }


      const std::unordered_map<triton::arch::register_e, const triton::arch::Register>& riscv32Cpu::getAllRegisters(void) const {
        return this->id2reg;
      }

      const std::unordered_map<triton::uint64, triton::uint8, IdentityHash<triton::uint64>>& riscv32Cpu::getConcreteMemory(void) const {
        return this->memory;
      }

      std::set<const triton::arch::Register*> riscv32Cpu::getParentRegisters(void) const {
        std::set<const triton::arch::Register*> ret;

        for (const auto& kv: this->id2reg) {
          auto regId = kv.first;
          const auto& reg = kv.second;

          /* Add GPR */
          if (reg.getSize() == this->gprSize())
            ret.insert(&reg);

          /* Add FPU */
          else if (this->isFPU(regId))
            ret.insert(&reg);
        }

        return ret;
      }


      const triton::arch::Register& riscv32Cpu::getRegister(triton::arch::register_e id) const {
        try {
          return this->id2reg.at(id);
        } catch (const std::out_of_range&) {
          throw triton::exceptions::Cpu("riscv32Cpu::getRegister(): Invalid register for this architecture.");
        }
      }


      const triton::arch::Register& riscv32Cpu::getRegister(const std::string& name) const {
        std::string lower = name;
        std::transform(lower.begin(), lower.end(), lower.begin(), [](unsigned char c){ return std::tolower(c); });
        try {
          return this->getRegister(this->name2id.at(lower));
        } catch (const std::out_of_range&) {
          throw triton::exceptions::Cpu("riscv32Cpu::getRegister(): Invalid register for this architecture.");
        }
      }


      const triton::arch::Register& riscv32Cpu::getParentRegister(const triton::arch::Register& reg) const {
        return this->getRegister(reg.getParent());
      }


      const triton::arch::Register& riscv32Cpu::getParentRegister(triton::arch::register_e id) const {
        return this->getParentRegister(this->getRegister(id));
      }


      const triton::arch::Register& riscv32Cpu::getProgramCounter(void) const {
        return this->getRegister(this->pcId);
      }


      const triton::arch::Register& riscv32Cpu::getStackPointer(void) const {
        return this->getRegister(this->spId);
      }

      void riscv32Cpu::disassembly(triton::arch::Instruction& inst) {

        triton::extlibs::capstone::cs_insn* insn;
        triton::usize count = 0;
        triton::uint32 size = 0;

        /* Check if the opcode and opcode' size are defined */
        if (inst.getOpcode() == nullptr || inst.getSize() == 0)
          throw triton::exceptions::Disassembly("riscv32Cpu::disassembly(): Opcode and opcodeSize must be definied.");

        /* Clear instructicon's operands if alredy defined */
        inst.operands.clear();

        /* Update instruction address if undefined */
        if (!inst.getAddress()) {
          inst.setAddress(static_cast<triton::uint32>(this->getConcreteRegisterValue(this->getProgramCounter())));
        }

        /* Let's disass and build our operands */
        count = triton::extlibs::capstone::cs_disasm(this->handle, inst.getOpcode(), inst.getSize(), inst.getAddress(), 0, &insn);
        if (count > 0) {
          /* Detail information */
          triton::extlibs::capstone::cs_detail* detail = insn->detail;

          /* Init the disassembly */
          std::stringstream str;

          str << insn[0].mnemonic;
          if (detail->riscv.op_count)
            str << " " <<  insn[0].op_str;

          inst.setDisassembly(str.str());

          /* Refine the size */
          inst.setSize(insn[0].size);

          /* Init the instruction's type */
          inst.setType(this->capstoneInstructionToTritonInstruction(insn[0].id));

          /* Set architecture */
          inst.setArchitecture(triton::arch::ARCH_RV32);

          /* Init operands */
          for (triton::uint32 n = 0; n < detail->riscv.op_count; n++) {
            triton::extlibs::capstone::cs_riscv_op* op = &(detail->riscv.operands[n]);

            switch(op->type) {

              case triton::extlibs::capstone::RISCV_OP_IMM: {
                triton::arch::Immediate imm(op->imm, size ? size : triton::size::dword);
                if (static_cast<triton::uint32>(op->imm) > imm.getValue()) {
                  imm = Immediate();
                  imm.setValue(op->imm, 0); /* By setting 0 as size, we automatically identify the size of the value */
                }

                inst.operands.push_back(triton::arch::OperandWrapper(imm));
                break;
              }

              case triton::extlibs::capstone::RISCV_OP_MEM: {
                triton::arch::MemoryAccess mem;

                 /* Set the size of the memory access */
                 size = this->getMemoryOperandSpecialSize(inst.getType());
                 mem.setBits(size ? ((size * triton::bitsize::byte) - 1) : triton::bitsize::dword - 1, 0);

                /* Set address calculation units */
                triton::arch::Register base(*this, this->capstoneRegisterToTritonRegister32(op->mem.base));

                triton::uint32 immsize = (
                  this->isRegisterValid(base.getId()) ? base.getSize() :
                  this->gprSize()
                );

                triton::arch::Immediate disp(op->mem.disp, immsize);

                mem.setBaseRegister(base);
                mem.setDisplacement(disp);

                inst.operands.push_back(triton::arch::OperandWrapper(mem));
                break;
              }

              case triton::extlibs::capstone::RISCV_OP_REG: {
                inst.operands.push_back(triton::arch::OperandWrapper(triton::arch::Register(*this, this->capstoneRegisterToTritonRegister32(op->reg))));
                break;
              }

              default:
                throw triton::exceptions::Disassembly("riscv32Cpu::disassembly(): Invalid operand.");
            } // switch
          } // for operand

          /* Set branch */
          if (detail->groups_count > 0) {
            for (triton::uint32 n = 0; n < detail->groups_count; n++) {
              if (detail->groups[n] == triton::extlibs::capstone::RISCV_GRP_JUMP)
                inst.setBranch(true);
              if (detail->groups[n] == triton::extlibs::capstone::RISCV_GRP_JUMP ||
                detail->groups[n] == triton::extlibs::capstone::RISCV_GRP_CALL ||
                detail->groups[n] == triton::extlibs::capstone::RISCV_GRP_RET)
              inst.setControlFlow(true);
            }
          }

          /* Free capstone stuffs */
          triton::extlibs::capstone::cs_free(insn, count);
        }
        else
          throw triton::exceptions::Disassembly("riscv32Cpu::disassembly(): Failed to disassemble the given code.");
      }


      triton::uint8 riscv32Cpu::getConcreteMemoryValue(triton::uint64 addr, bool execCallbacks) const {
        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, triton::size::byte));

        auto it = this->memory.find(addr);
        if (it == this->memory.end()) {
          return 0x00;
        }

        return it->second;
      }


      triton::uint512 riscv32Cpu::getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks) const {
        triton::uint512 ret = 0;
        triton::uint64 addr = 0;
        triton::uint32 size = 0;

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, mem);

        addr = mem.getAddress();
        size = mem.getSize();

        if (size == 0 || size > triton::size::dqqword)
          throw triton::exceptions::Cpu("riscv32Cpu::getConcreteMemoryValue(): Invalid size memory.");

        for (triton::sint32 i = size-1; i >= 0; i--)
          ret = ((ret << triton::bitsize::byte) | this->getConcreteMemoryValue(addr+i, false));

        return ret;
      }


      std::vector<triton::uint8> riscv32Cpu::getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks) const {
        std::vector<triton::uint8> area;

        for (triton::usize index = 0; index < size; index++)
          area.push_back(this->getConcreteMemoryValue(baseAddr+index, execCallbacks));

        return area;
      }


      triton::uint512 riscv32Cpu::getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks) const {
        triton::uint512 value = 0;

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_REGISTER_VALUE, reg);
        switch (reg.getId()) {
          case triton::arch::ID_REG_RV32_X0:   return 0;
          case triton::arch::ID_REG_RV32_X1:   return (*((triton::uint32*)(this->x1)));
          case triton::arch::ID_REG_RV32_SP:   return (*((triton::uint32*)(this->sp)));
          case triton::arch::ID_REG_RV32_X3:   return (*((triton::uint32*)(this->x3)));
          case triton::arch::ID_REG_RV32_X4:   return (*((triton::uint32*)(this->x4)));
          case triton::arch::ID_REG_RV32_X5:   return (*((triton::uint32*)(this->x5)));
          case triton::arch::ID_REG_RV32_X6:   return (*((triton::uint32*)(this->x6)));
          case triton::arch::ID_REG_RV32_X7:   return (*((triton::uint32*)(this->x7)));
          case triton::arch::ID_REG_RV32_X8:   return (*((triton::uint32*)(this->x8)));
          case triton::arch::ID_REG_RV32_X9:   return (*((triton::uint32*)(this->x9)));
          case triton::arch::ID_REG_RV32_X10:  return (*((triton::uint32*)(this->x10)));
          case triton::arch::ID_REG_RV32_X11:  return (*((triton::uint32*)(this->x11)));
          case triton::arch::ID_REG_RV32_X12:  return (*((triton::uint32*)(this->x12)));
          case triton::arch::ID_REG_RV32_X13:  return (*((triton::uint32*)(this->x13)));
          case triton::arch::ID_REG_RV32_X14:  return (*((triton::uint32*)(this->x14)));
          case triton::arch::ID_REG_RV32_X15:  return (*((triton::uint32*)(this->x15)));
          case triton::arch::ID_REG_RV32_X16:  return (*((triton::uint32*)(this->x16)));
          case triton::arch::ID_REG_RV32_X17:  return (*((triton::uint32*)(this->x17)));
          case triton::arch::ID_REG_RV32_X18:  return (*((triton::uint32*)(this->x18)));
          case triton::arch::ID_REG_RV32_X19:  return (*((triton::uint32*)(this->x19)));
          case triton::arch::ID_REG_RV32_X20:  return (*((triton::uint32*)(this->x20)));
          case triton::arch::ID_REG_RV32_X21:  return (*((triton::uint32*)(this->x21)));
          case triton::arch::ID_REG_RV32_X22:  return (*((triton::uint32*)(this->x22)));
          case triton::arch::ID_REG_RV32_X23:  return (*((triton::uint32*)(this->x23)));
          case triton::arch::ID_REG_RV32_X24:  return (*((triton::uint32*)(this->x24)));
          case triton::arch::ID_REG_RV32_X25:  return (*((triton::uint32*)(this->x25)));
          case triton::arch::ID_REG_RV32_X26:  return (*((triton::uint32*)(this->x26)));
          case triton::arch::ID_REG_RV32_X27:  return (*((triton::uint32*)(this->x27)));
          case triton::arch::ID_REG_RV32_X28:  return (*((triton::uint32*)(this->x28)));
          case triton::arch::ID_REG_RV32_X29:  return (*((triton::uint32*)(this->x29)));
          case triton::arch::ID_REG_RV32_X30:  return (*((triton::uint32*)(this->x30)));
          case triton::arch::ID_REG_RV32_X31:  return (*((triton::uint32*)(this->x31)));
          case triton::arch::ID_REG_RV32_PC:   return (*((triton::uint32*)(this->pc)));
          case triton::arch::ID_REG_RV32_F0:   return (*((triton::uint32*)(this->f0)));
          case triton::arch::ID_REG_RV32_F1:   return (*((triton::uint32*)(this->f1)));
          case triton::arch::ID_REG_RV32_F2:   return (*((triton::uint32*)(this->f2)));
          case triton::arch::ID_REG_RV32_F3:   return (*((triton::uint32*)(this->f3)));
          case triton::arch::ID_REG_RV32_F4:   return (*((triton::uint32*)(this->f4)));
          case triton::arch::ID_REG_RV32_F5:   return (*((triton::uint32*)(this->f5)));
          case triton::arch::ID_REG_RV32_F6:   return (*((triton::uint32*)(this->f6)));
          case triton::arch::ID_REG_RV32_F7:   return (*((triton::uint32*)(this->f7)));
          case triton::arch::ID_REG_RV32_F8:   return (*((triton::uint32*)(this->f8)));
          case triton::arch::ID_REG_RV32_F9:   return (*((triton::uint32*)(this->f9)));
          case triton::arch::ID_REG_RV32_F10:  return (*((triton::uint32*)(this->f10)));
          case triton::arch::ID_REG_RV32_F11:  return (*((triton::uint32*)(this->f11)));
          case triton::arch::ID_REG_RV32_F12:  return (*((triton::uint32*)(this->f12)));
          case triton::arch::ID_REG_RV32_F13:  return (*((triton::uint32*)(this->f13)));
          case triton::arch::ID_REG_RV32_F14:  return (*((triton::uint32*)(this->f14)));
          case triton::arch::ID_REG_RV32_F15:  return (*((triton::uint32*)(this->f15)));
          case triton::arch::ID_REG_RV32_F16:  return (*((triton::uint32*)(this->f16)));
          case triton::arch::ID_REG_RV32_F17:  return (*((triton::uint32*)(this->f17)));
          case triton::arch::ID_REG_RV32_F18:  return (*((triton::uint32*)(this->f18)));
          case triton::arch::ID_REG_RV32_F19:  return (*((triton::uint32*)(this->f19)));
          case triton::arch::ID_REG_RV32_F20:  return (*((triton::uint32*)(this->f20)));
          case triton::arch::ID_REG_RV32_F21:  return (*((triton::uint32*)(this->f21)));
          case triton::arch::ID_REG_RV32_F22:  return (*((triton::uint32*)(this->f22)));
          case triton::arch::ID_REG_RV32_F23:  return (*((triton::uint32*)(this->f23)));
          case triton::arch::ID_REG_RV32_F24:  return (*((triton::uint32*)(this->f24)));
          case triton::arch::ID_REG_RV32_F25:  return (*((triton::uint32*)(this->f25)));
          case triton::arch::ID_REG_RV32_F26:  return (*((triton::uint32*)(this->f26)));
          case triton::arch::ID_REG_RV32_F27:  return (*((triton::uint32*)(this->f27)));
          case triton::arch::ID_REG_RV32_F28:  return (*((triton::uint32*)(this->f28)));
          case triton::arch::ID_REG_RV32_F29:  return (*((triton::uint32*)(this->f29)));
          case triton::arch::ID_REG_RV32_F30:  return (*((triton::uint32*)(this->f30)));
          case triton::arch::ID_REG_RV32_F31:  return (*((triton::uint32*)(this->f31)));

          default:
            throw triton::exceptions::Cpu("riscv32Cpu::getConcreteRegisterValue(): Invalid register.");
        }

        return value;
      }


      void riscv32Cpu::setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value, bool execCallbacks) {
        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, triton::size::byte), value);
        this->memory[addr] = value;
      }


      void riscv32Cpu::setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value, bool execCallbacks) {
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();
        triton::uint512 cv  = value;

        if (cv > mem.getMaxValue())
          throw triton::exceptions::Register("riscv32Cpu::setConcreteMemoryValue(): You cannot set this concrete value (too big) to this memory access.");

        if (size == 0 || size > triton::size::dqqword)
          throw triton::exceptions::Cpu("riscv32Cpu::setConcreteMemoryValue(): Invalid size memory.");

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, mem, value);

        for (triton::uint32 i = 0; i < size; i++) {
          this->memory[addr+i] = static_cast<triton::uint8>((cv & 0xff));
          cv >>= 8;
        }
      }


      void riscv32Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values, bool execCallbacks) {
        // Pre-reserving the memory. We modified the original robin_map to not force rehash on reserve.
        this->memory.reserve(values.size() + this->memory.size());
        for (triton::usize index = 0; index < values.size(); index++) {
          this->setConcreteMemoryValue(baseAddr+index, values[index], execCallbacks);
        }
      }


      void riscv32Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const void* area, triton::usize size, bool execCallbacks) {
        // Pre-reserving the memory. We modified the original robin_map to not force rehash on every reserve if not needed.
        this->memory.reserve(size + this->memory.size());
        for (triton::usize index = 0; index < size; index++) {
          this->setConcreteMemoryValue(baseAddr+index, reinterpret_cast<const triton::uint8*>(area)[index], execCallbacks);
        }
      }


      void riscv32Cpu::setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value, bool execCallbacks) {
        if (value > reg.getMaxValue())
          throw triton::exceptions::Register("riscv32Cpu::setConcreteRegisterValue(): You cannot set this concrete value (too big) to this register.");

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_REGISTER_VALUE, reg, value);

        switch (reg.getId()) {
          case triton::arch::ID_REG_RV32_X0:   break;  // Always zero, just do nothing
          case triton::arch::ID_REG_RV32_X1:   (*((triton::uint32*)(this->x1)))   = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_SP:   (*((triton::uint32*)(this->sp)))   = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X3:   (*((triton::uint32*)(this->x3)))   = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X4:   (*((triton::uint32*)(this->x4)))   = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X5:   (*((triton::uint32*)(this->x5)))   = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X6:   (*((triton::uint32*)(this->x6)))   = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X7:   (*((triton::uint32*)(this->x7)))   = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X8:   (*((triton::uint32*)(this->x8)))   = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X9:   (*((triton::uint32*)(this->x9)))   = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X10:  (*((triton::uint32*)(this->x10)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X11:  (*((triton::uint32*)(this->x11)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X12:  (*((triton::uint32*)(this->x12)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X13:  (*((triton::uint32*)(this->x13)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X14:  (*((triton::uint32*)(this->x14)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X15:  (*((triton::uint32*)(this->x15)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X16:  (*((triton::uint32*)(this->x16)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X17:  (*((triton::uint32*)(this->x17)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X18:  (*((triton::uint32*)(this->x18)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X19:  (*((triton::uint32*)(this->x19)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X20:  (*((triton::uint32*)(this->x20)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X21:  (*((triton::uint32*)(this->x21)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X22:  (*((triton::uint32*)(this->x22)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X23:  (*((triton::uint32*)(this->x23)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X24:  (*((triton::uint32*)(this->x24)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X25:  (*((triton::uint32*)(this->x25)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X26:  (*((triton::uint32*)(this->x26)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X27:  (*((triton::uint32*)(this->x27)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X28:  (*((triton::uint32*)(this->x28)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X29:  (*((triton::uint32*)(this->x29)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X30:  (*((triton::uint32*)(this->x30)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_X31:  (*((triton::uint32*)(this->x31)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_PC:   (*((triton::uint32*)(this->pc)))   = static_cast<triton::uint32>(value); break;

          case triton::arch::ID_REG_RV32_F0:  (*((triton::uint32*)(this->f0)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F1:  (*((triton::uint32*)(this->f1)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F2:  (*((triton::uint32*)(this->f2)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F3:  (*((triton::uint32*)(this->f3)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F4:  (*((triton::uint32*)(this->f4)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F5:  (*((triton::uint32*)(this->f5)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F6:  (*((triton::uint32*)(this->f6)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F7:  (*((triton::uint32*)(this->f7)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F8:  (*((triton::uint32*)(this->f8)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F9:  (*((triton::uint32*)(this->f9)))  = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F10: (*((triton::uint32*)(this->f10))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F11: (*((triton::uint32*)(this->f11))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F12: (*((triton::uint32*)(this->f12))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F13: (*((triton::uint32*)(this->f13))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F14: (*((triton::uint32*)(this->f14))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F15: (*((triton::uint32*)(this->f15))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F16: (*((triton::uint32*)(this->f16))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F17: (*((triton::uint32*)(this->f17))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F18: (*((triton::uint32*)(this->f18))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F19: (*((triton::uint32*)(this->f19))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F20: (*((triton::uint32*)(this->f20))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F21: (*((triton::uint32*)(this->f21))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F22: (*((triton::uint32*)(this->f22))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F23: (*((triton::uint32*)(this->f23))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F24: (*((triton::uint32*)(this->f24))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F25: (*((triton::uint32*)(this->f25))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F26: (*((triton::uint32*)(this->f26))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F27: (*((triton::uint32*)(this->f27))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F28: (*((triton::uint32*)(this->f28))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F29: (*((triton::uint32*)(this->f29))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F30: (*((triton::uint32*)(this->f30))) = static_cast<triton::uint32>(value); break;
          case triton::arch::ID_REG_RV32_F31: (*((triton::uint32*)(this->f31))) = static_cast<triton::uint32>(value); break;

          default:
            throw triton::exceptions::Cpu("riscv32Cpu:setConcreteRegisterValue(): Invalid register.");

        }
      }


      bool riscv32Cpu::isThumb(void) const {
        /* There is no thumb mode in RV */
        return false;
      }


      void riscv32Cpu::setThumb(bool state) {
        /* There is no thumb mode in RV */
      }


      bool riscv32Cpu::isMemoryExclusive(const triton::arch::MemoryAccess& mem) const {
        /* There is no exclusive memory access support in RV */
        return false;
      }


      void riscv32Cpu::setMemoryExclusiveTag(const triton::arch::MemoryAccess& mem, bool tag) {
        /* There is no exclusive memory access support in RV */
      }


      bool riscv32Cpu::isConcreteMemoryValueDefined(const triton::arch::MemoryAccess& mem) const {
        return this->isConcreteMemoryValueDefined(mem.getAddress(), mem.getSize());
      }


      bool riscv32Cpu::isConcreteMemoryValueDefined(triton::uint64 baseAddr, triton::usize size) const {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) == this->memory.end()) {
            return false;
          }
        }
        return true;
      }


      void riscv32Cpu::clearConcreteMemoryValue(const triton::arch::MemoryAccess& mem) {
        this->clearConcreteMemoryValue(mem.getAddress(), mem.getSize());
      }


      void riscv32Cpu::clearConcreteMemoryValue(triton::uint64 baseAddr, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) != this->memory.end()) {
            this->memory.erase(baseAddr + index);
          }
        }
      }

    }; /* riscv namespace */
  }; /* arch namespace */
}; /* triton namespace */
