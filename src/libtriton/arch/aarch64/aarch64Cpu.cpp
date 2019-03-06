//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstring>

#include <triton/aarch64Cpu.hpp>
#include <triton/architecture.hpp>
#include <triton/coreUtils.hpp>
#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/externalLibs.hpp>
#include <triton/immediate.hpp>



namespace triton {
  namespace arch {
    namespace aarch64 {

      AArch64Cpu::AArch64Cpu(triton::callbacks::Callbacks* callbacks) : AArch64Specifications(ARCH_AARCH64) {
        this->callbacks = callbacks;
        this->clear();
      }


      AArch64Cpu::AArch64Cpu(const AArch64Cpu& other) : AArch64Specifications(ARCH_AARCH64) {
        this->copy(other);
      }


      AArch64Cpu::~AArch64Cpu() {
        this->memory.clear();
      }


      void AArch64Cpu::copy(const AArch64Cpu& other) {
        this->callbacks = other.callbacks;
        this->memory    = other.memory;

        std::memcpy(this->x0,   other.x0,   sizeof(this->x0));
        std::memcpy(this->x1,   other.x1,   sizeof(this->x1));
        std::memcpy(this->x2,   other.x2,   sizeof(this->x2));
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
        std::memcpy(this->sp,   other.sp,   sizeof(this->sp));
        std::memcpy(this->pc,   other.pc,   sizeof(this->pc));
        std::memcpy(this->spsr, other.spsr, sizeof(this->spsr));
      }


      void AArch64Cpu::clear(void) {
        /* Clear memory */
        this->memory.clear();

        /* Clear registers */
        std::memset(this->x0,   0x00, sizeof(this->x0));
        std::memset(this->x1,   0x00, sizeof(this->x1));
        std::memset(this->x2,   0x00, sizeof(this->x2));
        std::memset(this->x3,   0x00, sizeof(this->x3));
        std::memset(this->x4,   0x00, sizeof(this->x4));
        std::memset(this->x5,   0x00, sizeof(this->x5));
        std::memset(this->x6,   0x00, sizeof(this->x6));
        std::memset(this->x7,   0x00, sizeof(this->x7));
        std::memset(this->x8,   0x00, sizeof(this->x8));
        std::memset(this->x9,   0x00, sizeof(this->x9));
        std::memset(this->x10,  0x00, sizeof(this->x10));
        std::memset(this->x11,  0x00, sizeof(this->x11));
        std::memset(this->x12,  0x00, sizeof(this->x12));
        std::memset(this->x13,  0x00, sizeof(this->x13));
        std::memset(this->x14,  0x00, sizeof(this->x14));
        std::memset(this->x15,  0x00, sizeof(this->x15));
        std::memset(this->x16,  0x00, sizeof(this->x16));
        std::memset(this->x17,  0x00, sizeof(this->x17));
        std::memset(this->x18,  0x00, sizeof(this->x18));
        std::memset(this->x19,  0x00, sizeof(this->x19));
        std::memset(this->x20,  0x00, sizeof(this->x20));
        std::memset(this->x21,  0x00, sizeof(this->x21));
        std::memset(this->x22,  0x00, sizeof(this->x22));
        std::memset(this->x23,  0x00, sizeof(this->x23));
        std::memset(this->x24,  0x00, sizeof(this->x24));
        std::memset(this->x25,  0x00, sizeof(this->x25));
        std::memset(this->x26,  0x00, sizeof(this->x26));
        std::memset(this->x27,  0x00, sizeof(this->x27));
        std::memset(this->x28,  0x00, sizeof(this->x28));
        std::memset(this->x29,  0x00, sizeof(this->x29));
        std::memset(this->x30,  0x00, sizeof(this->x30));
        std::memset(this->sp,   0x00, sizeof(this->sp));
        std::memset(this->pc,   0x00, sizeof(this->pc));
        std::memset(this->spsr, 0x00, sizeof(this->spsr));
      }


      AArch64Cpu& AArch64Cpu::operator=(const AArch64Cpu& other) {
        this->copy(other);
        return *this;
      }


      triton::arch::endianness_e AArch64Cpu::getEndianness(void) const {
        return triton::arch::LE_ENDIANNESS;
      }


      bool AArch64Cpu::isFlag(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_AARCH64_C && regId <= triton::arch::ID_REG_AARCH64_Z) ? true : false);
      }


      bool AArch64Cpu::isRegister(triton::arch::register_e regId) const {
        return this->isGPR(regId);
      }


      bool AArch64Cpu::isRegisterValid(triton::arch::register_e regId) const {
        return (this->isFlag(regId) || this->isRegister(regId));
      }


      bool AArch64Cpu::isGPR(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_AARCH64_X0 && regId <= triton::arch::ID_REG_AARCH64_WZR) ? true : false);
      }


      triton::uint32 AArch64Cpu::numberOfRegisters(void) const {
        return triton::arch::ID_REG_LAST_ITEM;
      }


      triton::uint32 AArch64Cpu::gprSize(void) const {
        return QWORD_SIZE;
      }


      triton::uint32 AArch64Cpu::gprBitSize(void) const {
        return QWORD_SIZE_BIT;
      }


      const std::unordered_map<triton::arch::register_e, const triton::arch::Register>& AArch64Cpu::getAllRegisters(void) const {
        return this->registers_;
      }


      std::set<const triton::arch::Register*> AArch64Cpu::getParentRegisters(void) const {
        std::set<const triton::arch::Register*> ret;

        for (const auto& kv: this->registers_) {
          auto regId = kv.first;
          const auto& reg = kv.second;

          /* Add GPR */
          if (reg.getSize() == this->gprSize())
            ret.insert(&reg);

          /* Add Flags */
          else if (this->isFlag(regId))
            ret.insert(&reg);
        }

        return ret;
      }


      const triton::arch::Register& AArch64Cpu::getRegister(triton::arch::register_e id) const {
        try {
          return this->registers_.at(id);
        } catch (const std::out_of_range&) {
          throw triton::exceptions::Cpu("AArch64Cpu::getRegister(): Invalid register for this architecture.");
        }
      }


      const triton::arch::Register& AArch64Cpu::getParentRegister(const triton::arch::Register& reg) const {
        return this->getRegister(reg.getParent());
      }


      const triton::arch::Register& AArch64Cpu::getParentRegister(triton::arch::register_e id) const {
        return this->getParentRegister(this->getRegister(id));
      }


      const triton::arch::Register& AArch64Cpu::getProgramCounter(void) const {
        return this->getRegister(this->pcId);
      }


      const triton::arch::Register& AArch64Cpu::getStackPointer(void) const {
        return this->getRegister(this->spId);
      }


      void AArch64Cpu::disassembly(triton::arch::Instruction& inst) const {
        triton::extlibs::capstone::csh       handle;
        triton::extlibs::capstone::cs_insn*  insn;
        triton::usize                        count = 0;
        triton::uint32                       size = 0;

        /* Check if the opcode and opcode' size are defined */
        if (inst.getOpcode() == nullptr || inst.getSize() == 0)
          throw triton::exceptions::Disassembly("AArch64Cpu::disassembly(): Opcode and opcodeSize must be definied.");

        /* Open capstone */
        if (triton::extlibs::capstone::cs_open(triton::extlibs::capstone::CS_ARCH_ARM64, triton::extlibs::capstone::CS_MODE_ARM, &handle) != triton::extlibs::capstone::CS_ERR_OK)
          throw triton::exceptions::Disassembly("AArch64Cpu::disassembly(): Cannot open capstone.");

        /* Init capstone's options */
        triton::extlibs::capstone::cs_option(handle, triton::extlibs::capstone::CS_OPT_DETAIL, triton::extlibs::capstone::CS_OPT_ON);

        /* Clear instructicon's operands if alredy defined */
        inst.operands.clear();

        /* Let's disass and build our operands */
        count = triton::extlibs::capstone::cs_disasm(handle, inst.getOpcode(), inst.getSize(), inst.getAddress(), 0, &insn);
        if (count > 0) {
          triton::extlibs::capstone::cs_detail* detail = insn->detail;
          for (triton::uint32 j = 0; j < 1; j++) {

            /* Init the disassembly */
            std::stringstream str;

            /* Add mnemonic */
            str << insn[j].mnemonic;

            /* Add operands */
            if (detail->arm64.op_count)
              str << " " <<  insn[j].op_str;

            inst.setDisassembly(str.str());

            /* Refine the size */
            inst.setSize(insn[j].size);

            /* Init the instruction's type */
            inst.setType(this->capstoneInstructionToTritonInstruction(insn[j].id));

            /* Init the instruction's code codition */
            inst.setCodeCondition(this->capstoneConditionToTritonCondition(detail->arm64.cc));

            /* Init the instruction's write back flag */
            inst.setWriteBack(detail->arm64.writeback);

            /* Set True if the instruction udpate flags */
            inst.setUpdateFlag(detail->arm64.update_flags);

            /* Init operands */
            for (triton::uint32 n = 0; n < detail->arm64.op_count; n++) {
              triton::extlibs::capstone::cs_arm64_op* op = &(detail->arm64.operands[n]);
              switch(op->type) {

                case triton::extlibs::capstone::ARM64_OP_IMM: {
                  triton::arch::Immediate imm(op->imm, size ? size : QWORD_SIZE);

                  /* Set Shift type and value */
                  imm.setShiftType(this->capstoneShiftToTritonShift(op->shift.type));
                  imm.setShiftValue(op->shift.value);

                  inst.operands.push_back(triton::arch::OperandWrapper(imm));
                  break;
                }

                case triton::extlibs::capstone::ARM64_OP_MEM: {
                  triton::arch::MemoryAccess mem;

                  /* Set the size of the memory access */
                  mem.setPair(std::make_pair(size ? ((size * BYTE_SIZE_BIT) - 1) : QWORD_SIZE_BIT - 1, 0));

                  /* LEA if exists */
                  const triton::arch::Register base(*this, this->capstoneRegisterToTritonRegister(op->mem.base));
                  const triton::arch::Register index(*this, this->capstoneRegisterToTritonRegister(op->mem.index));

                  triton::uint32 immsize = (
                                            this->isRegisterValid(base.getId()) ? base.getSize() :
                                            this->isRegisterValid(index.getId()) ? index.getSize() :
                                            this->gprSize()
                                          );

                  triton::arch::Immediate disp(op->mem.disp, immsize);

                  /* Specify that LEA contains a PC relative */
                  /* FIXME: Valid in ARM64 ? */
                  if (base.getId() == this->pcId)
                    mem.setPcRelative(inst.getNextAddress());

                  /* Note that in ARM64 there is no segment register and scale value */
                  mem.setBaseRegister(base);
                  mem.setIndexRegister(index);
                  mem.setDisplacement(disp);

                  /* If there is an index register available, set scale to 1 to perform this following computation (base) + (index * scale) */
                  if (this->isRegisterValid(index.getId()))
                    mem.setScale(triton::arch::Immediate(1, index.getSize()));

                  inst.operands.push_back(triton::arch::OperandWrapper(mem));
                  break;
                }

                case triton::extlibs::capstone::ARM64_OP_REG: {
                  triton::arch::Register reg(*this, this->capstoneRegisterToTritonRegister(op->reg));

                  /* Set Shift type and value */
                  reg.setShiftType(this->capstoneShiftToTritonShift(op->shift.type));
                  reg.setShiftValue(op->shift.value);

                  /* Set extend type and size */
                  reg.setExtendType(this->capstoneExtendToTritonExtend(op->ext));
                  if (op->ext != triton::extlibs::capstone::ARM64_EXT_INVALID)
                    reg.setExtendedSize(size * BYTE_SIZE_BIT);

                  /* Define a base address for next operand */
                  if (!size)
                    size = reg.getSize();

                  inst.operands.push_back(triton::arch::OperandWrapper(reg));
                  break;
                }

                default:
                  /* FIXME: What about FP, C-IMM ? */
                  throw triton::exceptions::Disassembly("AArch64Cpu::disassembly(): Invalid operand.");
              } // switch
            } // for operand

            /* Set control flow */
            if (insn[j].id == triton::extlibs::capstone::ARM64_INS_RET)
              inst.setControlFlow(true);

          } // for instruction

          /* Set branch */
          if (detail->groups_count > 0) {
            for (triton::uint32 n = 0; n < detail->groups_count; n++) {
              if (detail->groups[n] == triton::extlibs::capstone::ARM64_GRP_JUMP) {
                inst.setBranch(true);
                inst.setControlFlow(true);
              }
            }
          }

          /* Free capstone stuffs */
          triton::extlibs::capstone::cs_free(insn, count);
        }
        else
          throw triton::exceptions::Disassembly("AArch64Cpu::disassembly(): Failed to disassemble the given code.");

        triton::extlibs::capstone::cs_close(&handle);
        return;
      }


      triton::uint8 AArch64Cpu::getConcreteMemoryValue(triton::uint64 addr, bool execCallbacks) const {
        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, BYTE_SIZE));

        auto it = this->memory.find(addr);
        if (it == this->memory.end())
          return 0x00;

        return it->second;
      }


      triton::uint512 AArch64Cpu::getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks) const {
        triton::uint512 ret = 0;
        triton::uint64 addr = 0;
        triton::uint32 size = 0;

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, mem);

        addr = mem.getAddress();
        size = mem.getSize();

        if (size == 0 || size > DQQWORD_SIZE)
          throw triton::exceptions::Cpu("AArch64Cpu::getConcreteMemoryValue(): Invalid size memory.");

        for (triton::sint32 i = size-1; i >= 0; i--)
          ret = ((ret << BYTE_SIZE_BIT) | this->getConcreteMemoryValue(addr+i, false));

        return ret;
      }


      std::vector<triton::uint8> AArch64Cpu::getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks) const {
        std::vector<triton::uint8> area;

        for (triton::usize index = 0; index < size; index++)
          area.push_back(this->getConcreteMemoryValue(baseAddr+index));

        return area;
      }


      triton::uint512 AArch64Cpu::getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks) const {
        triton::uint512 value = 0;

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_REGISTER_VALUE, reg);

        switch (reg.getId()) {
          case triton::arch::ID_REG_AARCH64_X0:   return (*((triton::uint64*)(this->x0)));
          case triton::arch::ID_REG_AARCH64_W0:   return (*((triton::uint32*)(this->x0)));
          case triton::arch::ID_REG_AARCH64_X1:   return (*((triton::uint64*)(this->x1)));
          case triton::arch::ID_REG_AARCH64_W1:   return (*((triton::uint32*)(this->x1)));
          case triton::arch::ID_REG_AARCH64_X2:   return (*((triton::uint64*)(this->x2)));
          case triton::arch::ID_REG_AARCH64_W2:   return (*((triton::uint32*)(this->x2)));
          case triton::arch::ID_REG_AARCH64_X3:   return (*((triton::uint64*)(this->x3)));
          case triton::arch::ID_REG_AARCH64_W3:   return (*((triton::uint32*)(this->x3)));
          case triton::arch::ID_REG_AARCH64_X4:   return (*((triton::uint64*)(this->x4)));
          case triton::arch::ID_REG_AARCH64_W4:   return (*((triton::uint32*)(this->x4)));
          case triton::arch::ID_REG_AARCH64_X5:   return (*((triton::uint64*)(this->x5)));
          case triton::arch::ID_REG_AARCH64_W5:   return (*((triton::uint32*)(this->x5)));
          case triton::arch::ID_REG_AARCH64_X6:   return (*((triton::uint64*)(this->x6)));
          case triton::arch::ID_REG_AARCH64_W6:   return (*((triton::uint32*)(this->x6)));
          case triton::arch::ID_REG_AARCH64_X7:   return (*((triton::uint64*)(this->x7)));
          case triton::arch::ID_REG_AARCH64_W7:   return (*((triton::uint32*)(this->x7)));
          case triton::arch::ID_REG_AARCH64_X8:   return (*((triton::uint64*)(this->x8)));
          case triton::arch::ID_REG_AARCH64_W8:   return (*((triton::uint32*)(this->x8)));
          case triton::arch::ID_REG_AARCH64_X9:   return (*((triton::uint64*)(this->x9)));
          case triton::arch::ID_REG_AARCH64_W9:   return (*((triton::uint32*)(this->x9)));
          case triton::arch::ID_REG_AARCH64_X10:  return (*((triton::uint64*)(this->x10)));
          case triton::arch::ID_REG_AARCH64_W10:  return (*((triton::uint32*)(this->x10)));
          case triton::arch::ID_REG_AARCH64_X11:  return (*((triton::uint64*)(this->x11)));
          case triton::arch::ID_REG_AARCH64_W11:  return (*((triton::uint32*)(this->x11)));
          case triton::arch::ID_REG_AARCH64_X12:  return (*((triton::uint64*)(this->x12)));
          case triton::arch::ID_REG_AARCH64_W12:  return (*((triton::uint32*)(this->x12)));
          case triton::arch::ID_REG_AARCH64_X13:  return (*((triton::uint64*)(this->x13)));
          case triton::arch::ID_REG_AARCH64_W13:  return (*((triton::uint32*)(this->x13)));
          case triton::arch::ID_REG_AARCH64_X14:  return (*((triton::uint64*)(this->x14)));
          case triton::arch::ID_REG_AARCH64_W14:  return (*((triton::uint32*)(this->x14)));
          case triton::arch::ID_REG_AARCH64_X15:  return (*((triton::uint64*)(this->x15)));
          case triton::arch::ID_REG_AARCH64_W15:  return (*((triton::uint32*)(this->x15)));
          case triton::arch::ID_REG_AARCH64_X16:  return (*((triton::uint64*)(this->x16)));
          case triton::arch::ID_REG_AARCH64_W16:  return (*((triton::uint32*)(this->x16)));
          case triton::arch::ID_REG_AARCH64_X17:  return (*((triton::uint64*)(this->x17)));
          case triton::arch::ID_REG_AARCH64_W17:  return (*((triton::uint32*)(this->x17)));
          case triton::arch::ID_REG_AARCH64_X18:  return (*((triton::uint64*)(this->x18)));
          case triton::arch::ID_REG_AARCH64_W18:  return (*((triton::uint32*)(this->x18)));
          case triton::arch::ID_REG_AARCH64_X19:  return (*((triton::uint64*)(this->x19)));
          case triton::arch::ID_REG_AARCH64_W19:  return (*((triton::uint32*)(this->x19)));
          case triton::arch::ID_REG_AARCH64_X20:  return (*((triton::uint64*)(this->x20)));
          case triton::arch::ID_REG_AARCH64_W20:  return (*((triton::uint32*)(this->x20)));
          case triton::arch::ID_REG_AARCH64_X21:  return (*((triton::uint64*)(this->x21)));
          case triton::arch::ID_REG_AARCH64_W21:  return (*((triton::uint32*)(this->x21)));
          case triton::arch::ID_REG_AARCH64_X22:  return (*((triton::uint64*)(this->x22)));
          case triton::arch::ID_REG_AARCH64_W22:  return (*((triton::uint32*)(this->x22)));
          case triton::arch::ID_REG_AARCH64_X23:  return (*((triton::uint64*)(this->x23)));
          case triton::arch::ID_REG_AARCH64_W23:  return (*((triton::uint32*)(this->x23)));
          case triton::arch::ID_REG_AARCH64_X24:  return (*((triton::uint64*)(this->x24)));
          case triton::arch::ID_REG_AARCH64_W24:  return (*((triton::uint32*)(this->x24)));
          case triton::arch::ID_REG_AARCH64_X25:  return (*((triton::uint64*)(this->x25)));
          case triton::arch::ID_REG_AARCH64_W25:  return (*((triton::uint32*)(this->x25)));
          case triton::arch::ID_REG_AARCH64_X26:  return (*((triton::uint64*)(this->x26)));
          case triton::arch::ID_REG_AARCH64_W26:  return (*((triton::uint32*)(this->x26)));
          case triton::arch::ID_REG_AARCH64_X27:  return (*((triton::uint64*)(this->x27)));
          case triton::arch::ID_REG_AARCH64_W27:  return (*((triton::uint32*)(this->x27)));
          case triton::arch::ID_REG_AARCH64_X28:  return (*((triton::uint64*)(this->x28)));
          case triton::arch::ID_REG_AARCH64_W28:  return (*((triton::uint32*)(this->x28)));
          case triton::arch::ID_REG_AARCH64_X29:  return (*((triton::uint64*)(this->x29)));
          case triton::arch::ID_REG_AARCH64_W29:  return (*((triton::uint32*)(this->x29)));
          case triton::arch::ID_REG_AARCH64_X30:  return (*((triton::uint64*)(this->x30)));
          case triton::arch::ID_REG_AARCH64_W30:  return (*((triton::uint32*)(this->x30)));
          case triton::arch::ID_REG_AARCH64_SP:   return (*((triton::uint64*)(this->sp)));
          case triton::arch::ID_REG_AARCH64_WSP:  return (*((triton::uint32*)(this->sp)));
          case triton::arch::ID_REG_AARCH64_PC:   return (*((triton::uint64*)(this->pc)));
          case triton::arch::ID_REG_AARCH64_XZR:  return 0;
          case triton::arch::ID_REG_AARCH64_WZR:  return 0;
          case triton::arch::ID_REG_AARCH64_SPSR: return (*((triton::uint32*)(this->spsr)));
          case triton::arch::ID_REG_AARCH64_N:    return (((*((triton::uint32*)(this->spsr))) >> 31) & 1);
          case triton::arch::ID_REG_AARCH64_Z:    return (((*((triton::uint32*)(this->spsr))) >> 30) & 1);
          case triton::arch::ID_REG_AARCH64_C:    return (((*((triton::uint32*)(this->spsr))) >> 29) & 1);
          case triton::arch::ID_REG_AARCH64_V:    return (((*((triton::uint32*)(this->spsr))) >> 28) & 1);
          default:
            throw triton::exceptions::Cpu("AArch64Cpu::getConcreteRegisterValue(): Invalid register.");
        }

        return value;
      }


      void AArch64Cpu::setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value) {
        if (this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, BYTE_SIZE), value);
        this->memory[addr] = value;
      }


      void AArch64Cpu::setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value) {
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();
        triton::uint512 cv  = value;

        if (cv > mem.getMaxValue())
          throw triton::exceptions::Register("AArch64Cpu::setConcreteMemoryValue(): You cannot set this concrete value (too big) to this memory access.");

        if (size == 0 || size > DQQWORD_SIZE)
          throw triton::exceptions::Cpu("AArch64Cpu::setConcreteMemoryValue(): Invalid size memory.");

        if (this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, mem, value);

        for (triton::uint32 i = 0; i < size; i++) {
          this->memory[addr+i] = (cv & 0xff).convert_to<triton::uint8>();
          cv >>= 8;
        }
      }


      void AArch64Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values) {
        for (triton::usize index = 0; index < values.size(); index++) {
          this->setConcreteMemoryValue(baseAddr+index, values[index]);
        }
      }


      void AArch64Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          this->setConcreteMemoryValue(baseAddr+index, area[index]);
        }
      }


      void AArch64Cpu::setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value) {
        if (value > reg.getMaxValue())
          throw triton::exceptions::Register("AArch64Cpu::setConcreteRegisterValue(): You cannot set this concrete value (too big) to this register.");

        if (this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_REGISTER_VALUE, reg, value);

        switch (reg.getId()) {
          case triton::arch::ID_REG_AARCH64_X0:   (*((triton::uint64*)(this->x0)))   = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W0:   (*((triton::uint32*)(this->x0)))   = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X1:   (*((triton::uint64*)(this->x1)))   = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W1:   (*((triton::uint32*)(this->x1)))   = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X2:   (*((triton::uint64*)(this->x2)))   = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W2:   (*((triton::uint32*)(this->x2)))   = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X3:   (*((triton::uint64*)(this->x3)))   = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W3:   (*((triton::uint32*)(this->x3)))   = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X4:   (*((triton::uint64*)(this->x4)))   = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W4:   (*((triton::uint32*)(this->x4)))   = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X5:   (*((triton::uint64*)(this->x5)))   = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W5:   (*((triton::uint32*)(this->x5)))   = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X6:   (*((triton::uint64*)(this->x6)))   = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W6:   (*((triton::uint32*)(this->x6)))   = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X7:   (*((triton::uint64*)(this->x7)))   = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W7:   (*((triton::uint32*)(this->x7)))   = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X8:   (*((triton::uint64*)(this->x8)))   = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W8:   (*((triton::uint32*)(this->x8)))   = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X9:   (*((triton::uint64*)(this->x9)))   = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W9:   (*((triton::uint32*)(this->x9)))   = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X10:  (*((triton::uint64*)(this->x10)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W10:  (*((triton::uint32*)(this->x10)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X11:  (*((triton::uint64*)(this->x11)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W11:  (*((triton::uint32*)(this->x11)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X12:  (*((triton::uint64*)(this->x12)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W12:  (*((triton::uint32*)(this->x12)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X13:  (*((triton::uint64*)(this->x13)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W13:  (*((triton::uint32*)(this->x13)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X14:  (*((triton::uint64*)(this->x14)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W14:  (*((triton::uint32*)(this->x14)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X15:  (*((triton::uint64*)(this->x15)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W15:  (*((triton::uint32*)(this->x15)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X16:  (*((triton::uint64*)(this->x16)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W16:  (*((triton::uint32*)(this->x16)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X17:  (*((triton::uint64*)(this->x17)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W17:  (*((triton::uint32*)(this->x17)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X18:  (*((triton::uint64*)(this->x18)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W18:  (*((triton::uint32*)(this->x18)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X19:  (*((triton::uint64*)(this->x19)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W19:  (*((triton::uint32*)(this->x19)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X20:  (*((triton::uint64*)(this->x20)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W20:  (*((triton::uint32*)(this->x20)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X21:  (*((triton::uint64*)(this->x21)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W21:  (*((triton::uint32*)(this->x21)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X22:  (*((triton::uint64*)(this->x22)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W22:  (*((triton::uint32*)(this->x22)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X23:  (*((triton::uint64*)(this->x23)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W23:  (*((triton::uint32*)(this->x23)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X24:  (*((triton::uint64*)(this->x24)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W24:  (*((triton::uint32*)(this->x24)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X25:  (*((triton::uint64*)(this->x25)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W25:  (*((triton::uint32*)(this->x25)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X26:  (*((triton::uint64*)(this->x26)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W26:  (*((triton::uint32*)(this->x26)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X27:  (*((triton::uint64*)(this->x27)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W27:  (*((triton::uint32*)(this->x27)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X28:  (*((triton::uint64*)(this->x28)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W28:  (*((triton::uint32*)(this->x28)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X29:  (*((triton::uint64*)(this->x29)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W29:  (*((triton::uint32*)(this->x29)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_X30:  (*((triton::uint64*)(this->x30)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_W30:  (*((triton::uint32*)(this->x30)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_SP:   (*((triton::uint64*)(this->sp)))   = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_WSP:  (*((triton::uint32*)(this->sp)))   = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_PC:   (*((triton::uint64*)(this->pc)))   = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_AARCH64_SPSR: (*((triton::uint32*)(this->spsr))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AARCH64_XZR:  break;  // Just do nothing
          case triton::arch::ID_REG_AARCH64_WZR:  break;  // Just do nothing
          case triton::arch::ID_REG_AARCH64_N: {
            triton::uint32 b = (*((triton::uint32*)(this->spsr)));
            (*((triton::uint32*)(this->spsr))) = !value.is_zero() ? b | (1 << 31) : b & ~(1 << 31);
            break;
          }
          case triton::arch::ID_REG_AARCH64_Z: {
            triton::uint32 b = (*((triton::uint32*)(this->spsr)));
            (*((triton::uint32*)(this->spsr))) = !value.is_zero() ? b | (1 << 30) : b & ~(1 << 30);
            break;
          }
          case triton::arch::ID_REG_AARCH64_C: {
            triton::uint32 b = (*((triton::uint32*)(this->spsr)));
            (*((triton::uint32*)(this->spsr))) = !value.is_zero() ? b | (1 << 29) : b & ~(1 << 29);
            break;
          }
          case triton::arch::ID_REG_AARCH64_V: {
            triton::uint32 b = (*((triton::uint32*)(this->spsr)));
            (*((triton::uint32*)(this->spsr))) = !value.is_zero() ? b | (1 << 28) : b & ~(1 << 28);
            break;
          }
          default:
            throw triton::exceptions::Cpu("AArch64Cpu:setConcreteRegisterValue(): Invalid register.");
        }
      }


      bool AArch64Cpu::isMemoryMapped(triton::uint64 baseAddr, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) == this->memory.end())
            return false;
        }
        return true;
      }


      void AArch64Cpu::unmapMemory(triton::uint64 baseAddr, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) != this->memory.end())
            this->memory.erase(baseAddr + index);
        }
      }

    }; /* x86 namespace */
  }; /* arch namespace */
}; /* triton namespace */
