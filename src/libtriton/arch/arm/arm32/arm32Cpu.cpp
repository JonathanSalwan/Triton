//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstring>

#include <triton/architecture.hpp>
#include <triton/arm32Cpu.hpp>
#include <triton/coreUtils.hpp>
#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/externalLibs.hpp>
#include <triton/immediate.hpp>



namespace triton {
  namespace arch {
    namespace arm {
      namespace arm32 {

        Arm32Cpu::Arm32Cpu(triton::callbacks::Callbacks* callbacks) : Arm32Specifications(ARCH_ARM32) {
          this->callbacks = callbacks;
          this->thumb = false;
          this->clear();
        }


        Arm32Cpu::Arm32Cpu(const Arm32Cpu& other) : Arm32Specifications(ARCH_ARM32) {
          this->copy(other);
        }


        Arm32Cpu::~Arm32Cpu() {
          this->memory.clear();
        }


        void Arm32Cpu::copy(const Arm32Cpu& other) {
          this->callbacks = other.callbacks;
          this->memory    = other.memory;

          std::memcpy(this->r0,   other.r0,   sizeof(this->r0));
          std::memcpy(this->r1,   other.r1,   sizeof(this->r1));
          std::memcpy(this->r2,   other.r2,   sizeof(this->r2));
          std::memcpy(this->r3,   other.r3,   sizeof(this->r3));
          std::memcpy(this->r4,   other.r4,   sizeof(this->r4));
          std::memcpy(this->r5,   other.r5,   sizeof(this->r5));
          std::memcpy(this->r6,   other.r6,   sizeof(this->r6));
          std::memcpy(this->r7,   other.r7,   sizeof(this->r7));
          std::memcpy(this->r8,   other.r8,   sizeof(this->r8));
          std::memcpy(this->r9,   other.r9,   sizeof(this->r9));
          std::memcpy(this->r10,  other.r10,  sizeof(this->r10));
          std::memcpy(this->r11,  other.r11,  sizeof(this->r11));
          std::memcpy(this->r12,  other.r12,  sizeof(this->r12));
          std::memcpy(this->sp,   other.sp,   sizeof(this->sp));
          std::memcpy(this->r14,  other.r14,  sizeof(this->r14));
          std::memcpy(this->pc,   other.pc,   sizeof(this->pc));
          std::memcpy(this->apsr, other.apsr, sizeof(this->apsr));
        }


        void Arm32Cpu::clear(void) {
          /* Clear memory */
          this->memory.clear();

          /* Clear registers */
          std::memset(this->r0,   0x00, sizeof(this->r0));
          std::memset(this->r1,   0x00, sizeof(this->r1));
          std::memset(this->r2,   0x00, sizeof(this->r2));
          std::memset(this->r3,   0x00, sizeof(this->r3));
          std::memset(this->r4,   0x00, sizeof(this->r4));
          std::memset(this->r5,   0x00, sizeof(this->r5));
          std::memset(this->r6,   0x00, sizeof(this->r6));
          std::memset(this->r7,   0x00, sizeof(this->r7));
          std::memset(this->r8,   0x00, sizeof(this->r8));
          std::memset(this->r9,   0x00, sizeof(this->r9));
          std::memset(this->r10,  0x00, sizeof(this->r10));
          std::memset(this->r11,  0x00, sizeof(this->r11));
          std::memset(this->r12,  0x00, sizeof(this->r12));
          std::memset(this->sp,   0x00, sizeof(this->sp));
          std::memset(this->r14,  0x00, sizeof(this->r14));
          std::memset(this->pc,   0x00, sizeof(this->pc));
          std::memset(this->apsr, 0x00, sizeof(this->apsr));
        }


        Arm32Cpu& Arm32Cpu::operator=(const Arm32Cpu& other) {
          this->copy(other);
          return *this;
        }


        triton::arch::endianness_e Arm32Cpu::getEndianness(void) const {
          return triton::arch::LE_ENDIANNESS;
        }


        bool Arm32Cpu::isFlag(triton::arch::register_e regId) const {
          return ((regId >= triton::arch::ID_REG_ARM32_C && regId <= triton::arch::ID_REG_ARM32_Z) ? true : false);
        }


        bool Arm32Cpu::isRegister(triton::arch::register_e regId) const {
          return this->isGPR(regId);
        }


        bool Arm32Cpu::isRegisterValid(triton::arch::register_e regId) const {
          return (this->isFlag(regId) || this->isRegister(regId));
        }


        bool Arm32Cpu::isGPR(triton::arch::register_e regId) const {
          return ((regId >= triton::arch::ID_REG_ARM32_R0 && regId <= triton::arch::ID_REG_ARM32_APSR) ? true : false);
        }


        triton::uint32 Arm32Cpu::numberOfRegisters(void) const {
          return triton::arch::ID_REG_LAST_ITEM;
        }


        triton::uint32 Arm32Cpu::gprSize(void) const {
          return DWORD_SIZE;
        }


        triton::uint32 Arm32Cpu::gprBitSize(void) const {
          return DWORD_SIZE_BIT;
        }


        const std::unordered_map<triton::arch::register_e, const triton::arch::Register>& Arm32Cpu::getAllRegisters(void) const {
          return this->registers_;
        }


        std::set<const triton::arch::Register*> Arm32Cpu::getParentRegisters(void) const {
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


        const triton::arch::Register& Arm32Cpu::getRegister(triton::arch::register_e id) const {
          try {
            return this->registers_.at(id);
          } catch (const std::out_of_range&) {
            throw triton::exceptions::Cpu("Arm32Cpu::getRegister(): Invalid register for this architecture.");
          }
        }


        const triton::arch::Register& Arm32Cpu::getParentRegister(const triton::arch::Register& reg) const {
          return this->getRegister(reg.getParent());
        }


        const triton::arch::Register& Arm32Cpu::getParentRegister(triton::arch::register_e id) const {
          return this->getParentRegister(this->getRegister(id));
        }


        const triton::arch::Register& Arm32Cpu::getProgramCounter(void) const {
          return this->getRegister(this->pcId);
        }


        const triton::arch::Register& Arm32Cpu::getStackPointer(void) const {
          return this->getRegister(this->spId);
        }


        void Arm32Cpu::disassembly(triton::arch::Instruction& inst) const {
          triton::extlibs::capstone::csh       handle;
          triton::extlibs::capstone::cs_mode   mode;
          triton::extlibs::capstone::cs_insn*  insn;
          triton::usize                        count = 0;

          /* Check if the opcode and opcode' size are defined */
          if (inst.getOpcode() == nullptr || inst.getSize() == 0)
            throw triton::exceptions::Disassembly("Arm32Cpu::disassembly(): Opcode and opcodeSize must be definied.");

          /* Open capstone */
          mode = this->thumb ? triton::extlibs::capstone::CS_MODE_THUMB : triton::extlibs::capstone::CS_MODE_ARM;

          if (triton::extlibs::capstone::cs_open(triton::extlibs::capstone::CS_ARCH_ARM, mode, &handle) != triton::extlibs::capstone::CS_ERR_OK)
            throw triton::exceptions::Disassembly("Arm32Cpu::disassembly(): Cannot open capstone.");

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
              if (detail->arm.op_count)
                str << " " <<  insn[j].op_str;

              inst.setDisassembly(str.str());

              /* Refine the size */
              inst.setSize(insn[j].size);

              /* Init the instruction's type */
              inst.setType(this->capstoneInstructionToTritonInstruction(insn[j].id));

              /* Init the instruction's code codition */
              inst.setCodeCondition(this->capstoneConditionToTritonCondition(detail->arm.cc));

              /* Init the instruction's write back flag */
              inst.setWriteBack(detail->arm.writeback);

              /* Set True if the instruction udpate flags */
              inst.setUpdateFlag(detail->arm.update_flags);

              /* Set thumb mode */
              inst.setThumb(thumb);

              /* Init operands */
              for (triton::uint32 n = 0; n < detail->arm.op_count; n++) {
                triton::extlibs::capstone::cs_arm_op* op = &(detail->arm.operands[n]);
                switch(op->type) {

                  case triton::extlibs::capstone::ARM_OP_IMM: {
                    triton::arch::Immediate imm(op->imm, DWORD_SIZE);

                    if (op->subtracted)
                      imm.setSubtracted(true);

                    inst.operands.push_back(triton::arch::OperandWrapper(imm));
                    break;
                  }

                  case triton::extlibs::capstone::ARM_OP_MEM: {
                    triton::arch::MemoryAccess mem;

                    /* Set the size of the memory access */
                    mem.setPair(std::make_pair(DWORD_SIZE_BIT-1, 0));

                    /* LEA if exists */
                    const triton::arch::Register base(*this, this->capstoneRegisterToTritonRegister(op->mem.base));
                    triton::arch::Register index(*this, this->capstoneRegisterToTritonRegister(op->mem.index));

                    /* Set Shift type and value */
                    triton::arch::arm::shift_e shiftType = this->capstoneShiftToTritonShift(op->shift.type);

                    index.setShiftType(shiftType);

                    switch(shiftType) {
                      case triton::arch::arm::ID_SHIFT_INVALID:
                        break;
                      case triton::arch::arm::ID_SHIFT_ASR:
                      case triton::arch::arm::ID_SHIFT_LSL:
                      case triton::arch::arm::ID_SHIFT_LSR:
                      case triton::arch::arm::ID_SHIFT_ROR:
                        index.setShiftValue(op->shift.value);
                        break;
                      case triton::arch::arm::ID_SHIFT_RRX:
                        /* NOTE: According to the manual RRX there is no
                         * immediate associated with this shift type. However,
                         * from the description of the instruction it can be
                         * deduced that a value of one is used.
                         */
                        index.setShiftValue(1);
                        break;
                      case triton::arch::arm::ID_SHIFT_ASR_REG:
                      case triton::arch::arm::ID_SHIFT_LSL_REG:
                      case triton::arch::arm::ID_SHIFT_LSR_REG:
                      case triton::arch::arm::ID_SHIFT_ROR_REG:
                        index.setShiftValue(this->capstoneRegisterToTritonRegister(op->shift.value));
                        break;
                      case triton::arch::arm::ID_SHIFT_RRX_REG:
                        /* NOTE: Capstone considers this as a viable shift operand
                         * but according to the ARM manual this is not possible.
                         */
                        throw triton::exceptions::Disassembly("Arm32Cpu::disassembly(): Invalid shift type.");
                        break;
                      default:
                        throw triton::exceptions::Disassembly("Arm32Cpu::disassembly(): Invalid shift type.");
                    }

                    if (op->subtracted)
                      index.setSubtracted(true);

                    triton::uint32 immsize = (
                                              this->isRegisterValid(base.getId()) ? base.getSize() :
                                              this->isRegisterValid(index.getId()) ? index.getSize() :
                                              this->gprSize()
                                            );

                    triton::arch::Immediate disp(op->mem.disp, immsize);

                    /* Specify that LEA contains a PC relative */
                    if (base.getId() == this->pcId) {
                      /* NOTE: PC always points to the address to the current
                       * instruction plus: a) 8 in case of ARM mode, or b) 4 in
                       * case of Thumb. It is also aligned to 4 bytes. For more
                       * information, refer to section "Use of labels in UAL
                       * instruction syntax" of the reference manual.
                       */
                      auto offset = this->thumb ? 4 : 8;
                      auto address = (inst.getAddress() + offset) & 0xfffffffc;
                      mem.setPcRelative(address);
                    }

                    /* Note that in ARM32 there is no segment register and scale value */
                    mem.setBaseRegister(base);
                    mem.setIndexRegister(index);
                    mem.setDisplacement(disp);

                    /* If there is an index register available, set scale to 1 to perform this following computation (base) + (index * scale) */
                    if (this->isRegisterValid(index.getId()))
                      mem.setScale(triton::arch::Immediate(1, index.getSize()));

                    inst.operands.push_back(triton::arch::OperandWrapper(mem));
                    break;
                  }

                  case triton::extlibs::capstone::ARM_OP_REG: {
                    triton::arch::Register reg(*this, this->capstoneRegisterToTritonRegister(op->reg));

                    /* Set Shift type and value */
                    triton::arch::arm::shift_e shiftType = this->capstoneShiftToTritonShift(op->shift.type);

                    reg.setShiftType(shiftType);

                    switch(shiftType) {
                      case triton::arch::arm::ID_SHIFT_INVALID:
                        break;
                      case triton::arch::arm::ID_SHIFT_ASR:
                      case triton::arch::arm::ID_SHIFT_LSL:
                      case triton::arch::arm::ID_SHIFT_LSR:
                      case triton::arch::arm::ID_SHIFT_ROR:
                        reg.setShiftValue(op->shift.value);
                        break;
                      case triton::arch::arm::ID_SHIFT_RRX:
                        /* NOTE: According to the manual RRX there is no
                         * immediate associated with this shift type. However,
                         * from the description of the instruction it can be
                         * deduced that a value of one is used.
                         */
                        reg.setShiftValue(1);
                        break;
                      case triton::arch::arm::ID_SHIFT_ASR_REG:
                      case triton::arch::arm::ID_SHIFT_LSL_REG:
                      case triton::arch::arm::ID_SHIFT_LSR_REG:
                      case triton::arch::arm::ID_SHIFT_ROR_REG:
                        reg.setShiftValue(this->capstoneRegisterToTritonRegister(op->shift.value));
                        break;
                      case triton::arch::arm::ID_SHIFT_RRX_REG:
                        /* NOTE: Capstone considers this as a viable shift operand
                         * but according to the ARM manual this is not possible.
                         */
                        throw triton::exceptions::Disassembly("Arm32Cpu::disassembly(): Invalid shift type.");
                        break;
                      default:
                        throw triton::exceptions::Disassembly("Arm32Cpu::disassembly(): Invalid shift type.");
                    }

                    if (op->subtracted)
                      reg.setSubtracted(true);

                    inst.operands.push_back(triton::arch::OperandWrapper(reg));
                    break;
                  }

                  default:
                    /* FIXME: What about FP, C-IMM ? */
                    throw triton::exceptions::Disassembly("Arm32Cpu::disassembly(): Invalid operand.");
                } // switch
              } // for operand
            } // for instruction

            /* Set branch */
            if (detail->groups_count > 0) {
              for (triton::uint32 n = 0; n < detail->groups_count; n++) {
                if (detail->groups[n] == triton::extlibs::capstone::ARM_GRP_JUMP) {
                  inst.setBranch(true);
                  inst.setControlFlow(true);
                }
              }
            }

            /* Post process instruction */
            this->postDisassembly(inst);

            /* Free capstone stuffs */
            triton::extlibs::capstone::cs_free(insn, count);
          }
          else
            throw triton::exceptions::Disassembly("Arm32Cpu::disassembly(): Failed to disassemble the given code.");

          triton::extlibs::capstone::cs_close(&handle);
          return;
        }


        void Arm32Cpu::postDisassembly(triton::arch::Instruction& inst) const {
          /* Fix update flag */
          /* FIXME: Quick (and super ugly) hack. Capstone is reporting
           * update_flags equals true for ADC, RSC and SBC instruction when
           * it shouldn't (it should only report true when the S suffix is
           * present).
           */
          switch (inst.getType()) {
            case ID_INS_ADC:
            case ID_INS_RSC:
            case ID_INS_SBC:
              if (inst.getDisassembly().at(3) != 's')
                inst.setUpdateFlag(false);
              break;
          }

          /* Make implicit destination operand explicit */
          /* NOTE: For some instructions the destination operand is
           * optional (in which case the first source operand is used as
           * destination). Capstone returns always all three operands for
           * ARM instruction (i.e. make the destination operand explicit).
           * However, it does not do the same for Thumb instructions. Here
           * we make the destination operand explicit (in order to simplify
           * the implementation of the semantics).
           */
          if (inst.isThumb() && inst.operands.size() == 2) {
            triton::arch::OperandWrapper op(inst.operands[0]);

            switch (inst.getType()) {
              case ID_INS_ADC:
              case ID_INS_ADD:
              case ID_INS_AND:
              case ID_INS_ASR:
              case ID_INS_BIC:
              case ID_INS_EOR:
              case ID_INS_LSL:
              case ID_INS_LSR:
              case ID_INS_ORR:
              case ID_INS_ROR:
              case ID_INS_SBC:
              case ID_INS_SUB:
                inst.operands.insert(inst.operands.begin(), op);
                break;
            }
          }
        }


        triton::uint8 Arm32Cpu::getConcreteMemoryValue(triton::uint64 addr, bool execCallbacks) const {
          if (execCallbacks && this->callbacks)
            this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, BYTE_SIZE));

          auto it = this->memory.find(addr);
          if (it == this->memory.end())
            return 0x00;

          return it->second;
        }


        triton::uint512 Arm32Cpu::getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks) const {
          triton::uint512 ret = 0;
          triton::uint64 addr = 0;
          triton::uint32 size = 0;

          if (execCallbacks && this->callbacks)
            this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, mem);

          addr = mem.getAddress();
          size = mem.getSize();

          if (size == 0 || size > DQQWORD_SIZE)
            throw triton::exceptions::Cpu("Arm32Cpu::getConcreteMemoryValue(): Invalid size memory.");

          for (triton::sint32 i = size-1; i >= 0; i--)
            ret = ((ret << BYTE_SIZE_BIT) | this->getConcreteMemoryValue(addr+i, false));

          return ret;
        }


        std::vector<triton::uint8> Arm32Cpu::getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks) const {
          std::vector<triton::uint8> area;

          for (triton::usize index = 0; index < size; index++)
            area.push_back(this->getConcreteMemoryValue(baseAddr+index));

          return area;
        }


        triton::uint512 Arm32Cpu::getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks) const {
          triton::uint512 value = 0;

          if (execCallbacks && this->callbacks)
            this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_REGISTER_VALUE, reg);

          switch (reg.getId()) {
            case triton::arch::ID_REG_ARM32_R0:   return (*((triton::uint32*)(this->r0)));
            case triton::arch::ID_REG_ARM32_R1:   return (*((triton::uint32*)(this->r1)));
            case triton::arch::ID_REG_ARM32_R2:   return (*((triton::uint32*)(this->r2)));
            case triton::arch::ID_REG_ARM32_R3:   return (*((triton::uint32*)(this->r3)));
            case triton::arch::ID_REG_ARM32_R4:   return (*((triton::uint32*)(this->r4)));
            case triton::arch::ID_REG_ARM32_R5:   return (*((triton::uint32*)(this->r5)));
            case triton::arch::ID_REG_ARM32_R6:   return (*((triton::uint32*)(this->r6)));
            case triton::arch::ID_REG_ARM32_R7:   return (*((triton::uint32*)(this->r7)));
            case triton::arch::ID_REG_ARM32_R8:   return (*((triton::uint32*)(this->r8)));
            case triton::arch::ID_REG_ARM32_R9:   return (*((triton::uint32*)(this->r9)));
            case triton::arch::ID_REG_ARM32_R10:  return (*((triton::uint32*)(this->r10)));
            case triton::arch::ID_REG_ARM32_R11:  return (*((triton::uint32*)(this->r11)));
            case triton::arch::ID_REG_ARM32_R12:  return (*((triton::uint32*)(this->r12)));
            case triton::arch::ID_REG_ARM32_SP:   return (*((triton::uint32*)(this->sp)));
            case triton::arch::ID_REG_ARM32_R14:  return (*((triton::uint32*)(this->r14)));
            case triton::arch::ID_REG_ARM32_PC:   return (*((triton::uint32*)(this->pc)));
            case triton::arch::ID_REG_ARM32_APSR: return (*((triton::uint32*)(this->apsr)));
            case triton::arch::ID_REG_ARM32_N:    return (((*((triton::uint32*)(this->apsr))) >> 31) & 1);
            case triton::arch::ID_REG_ARM32_Z:    return (((*((triton::uint32*)(this->apsr))) >> 30) & 1);
            case triton::arch::ID_REG_ARM32_C:    return (((*((triton::uint32*)(this->apsr))) >> 29) & 1);
            case triton::arch::ID_REG_ARM32_V:    return (((*((triton::uint32*)(this->apsr))) >> 28) & 1);
            default:
              throw triton::exceptions::Cpu("Arm32Cpu::getConcreteRegisterValue(): Invalid register.");
          }

          return value;
        }


        void Arm32Cpu::setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value) {
          if (this->callbacks)
            this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, BYTE_SIZE), value);
          this->memory[addr] = value;
        }


        void Arm32Cpu::setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value) {
          triton::uint64 addr = mem.getAddress();
          triton::uint32 size = mem.getSize();
          triton::uint512 cv  = value;

          if (cv > mem.getMaxValue())
            throw triton::exceptions::Register("Arm32Cpu::setConcreteMemoryValue(): You cannot set this concrete value (too big) to this memory access.");

          if (size == 0 || size > DQQWORD_SIZE)
            throw triton::exceptions::Cpu("Arm32Cpu::setConcreteMemoryValue(): Invalid size memory.");

          if (this->callbacks)
            this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, mem, value);

          for (triton::uint32 i = 0; i < size; i++) {
            this->memory[addr+i] = (cv & 0xff).convert_to<triton::uint8>();
            cv >>= 8;
          }
        }


        void Arm32Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values) {
          for (triton::usize index = 0; index < values.size(); index++) {
            this->setConcreteMemoryValue(baseAddr+index, values[index]);
          }
        }


        void Arm32Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size) {
          for (triton::usize index = 0; index < size; index++) {
            this->setConcreteMemoryValue(baseAddr+index, area[index]);
          }
        }


        void Arm32Cpu::setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value) {
          if (value > reg.getMaxValue())
            throw triton::exceptions::Register("Arm32Cpu::setConcreteRegisterValue(): You cannot set this concrete value (too big) to this register.");

          if (this->callbacks)
            this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_REGISTER_VALUE, reg, value);

          switch (reg.getId()) {
            case triton::arch::ID_REG_ARM32_R0:   (*((triton::uint32*)(this->r0)))   = value.convert_to<triton::uint32>(); break;
            case triton::arch::ID_REG_ARM32_R1:   (*((triton::uint32*)(this->r1)))   = value.convert_to<triton::uint32>(); break;
            case triton::arch::ID_REG_ARM32_R2:   (*((triton::uint32*)(this->r2)))   = value.convert_to<triton::uint32>(); break;
            case triton::arch::ID_REG_ARM32_R3:   (*((triton::uint32*)(this->r3)))   = value.convert_to<triton::uint32>(); break;
            case triton::arch::ID_REG_ARM32_R4:   (*((triton::uint32*)(this->r4)))   = value.convert_to<triton::uint32>(); break;
            case triton::arch::ID_REG_ARM32_R5:   (*((triton::uint32*)(this->r5)))   = value.convert_to<triton::uint32>(); break;
            case triton::arch::ID_REG_ARM32_R6:   (*((triton::uint32*)(this->r6)))   = value.convert_to<triton::uint32>(); break;
            case triton::arch::ID_REG_ARM32_R7:   (*((triton::uint32*)(this->r7)))   = value.convert_to<triton::uint32>(); break;
            case triton::arch::ID_REG_ARM32_R8:   (*((triton::uint32*)(this->r8)))   = value.convert_to<triton::uint32>(); break;
            case triton::arch::ID_REG_ARM32_R9:   (*((triton::uint32*)(this->r9)))   = value.convert_to<triton::uint32>(); break;
            case triton::arch::ID_REG_ARM32_R10:  (*((triton::uint32*)(this->r10)))  = value.convert_to<triton::uint32>(); break;
            case triton::arch::ID_REG_ARM32_R11:  (*((triton::uint32*)(this->r11)))  = value.convert_to<triton::uint32>(); break;
            case triton::arch::ID_REG_ARM32_R12:  (*((triton::uint32*)(this->r12)))  = value.convert_to<triton::uint32>(); break;
            case triton::arch::ID_REG_ARM32_SP:   (*((triton::uint32*)(this->sp)))   = value.convert_to<triton::uint32>(); break;
            case triton::arch::ID_REG_ARM32_R14:  (*((triton::uint32*)(this->r14)))  = value.convert_to<triton::uint32>(); break;
            case triton::arch::ID_REG_ARM32_PC: {
              /* NOTE: Once in Thumb mode only switch to ARM through a Branch
               * and Exchange instruction. The reason for this is that after
               * switching to Thumb the ISB (instruction set selection bit) is
               * cleared. Therefore, if we allow to switch back to ARM through
               * these mechanism we would have a problem processing Thumb
               * instructions.
               */
              auto pc = value.convert_to<triton::uint32>();
              if (this->isThumb() == false && (pc & 0x1) == 0x1) {
                this->setThumb(true);
              }
              (*((triton::uint32*)(this->pc))) = pc & ~0x1;
              break;
            }
            case triton::arch::ID_REG_ARM32_APSR: (*((triton::uint32*)(this->apsr))) = value.convert_to<triton::uint32>(); break;
            case triton::arch::ID_REG_ARM32_N: {
              triton::uint32 b = (*((triton::uint32*)(this->apsr)));
              (*((triton::uint32*)(this->apsr))) = !value.is_zero() ? b | (1 << 31) : b & ~(1 << 31);
              break;
            }
            case triton::arch::ID_REG_ARM32_Z: {
              triton::uint32 b = (*((triton::uint32*)(this->apsr)));
              (*((triton::uint32*)(this->apsr))) = !value.is_zero() ? b | (1 << 30) : b & ~(1 << 30);
              break;
            }
            case triton::arch::ID_REG_ARM32_C: {
              triton::uint32 b = (*((triton::uint32*)(this->apsr)));
              (*((triton::uint32*)(this->apsr))) = !value.is_zero() ? b | (1 << 29) : b & ~(1 << 29);
              break;
            }
            case triton::arch::ID_REG_ARM32_V: {
              triton::uint32 b = (*((triton::uint32*)(this->apsr)));
              (*((triton::uint32*)(this->apsr))) = !value.is_zero() ? b | (1 << 28) : b & ~(1 << 28);
              break;
            }
            default:
              throw triton::exceptions::Cpu("Arm32Cpu:setConcreteRegisterValue(): Invalid register.");
          }
        }


        bool Arm32Cpu::isMemoryMapped(triton::uint64 baseAddr, triton::usize size) {
          for (triton::usize index = 0; index < size; index++) {
            if (this->memory.find(baseAddr + index) == this->memory.end())
              return false;
          }
          return true;
        }


        void Arm32Cpu::unmapMemory(triton::uint64 baseAddr, triton::usize size) {
          for (triton::usize index = 0; index < size; index++) {
            if (this->memory.find(baseAddr + index) != this->memory.end())
              this->memory.erase(baseAddr + index);
          }
        }


        bool Arm32Cpu::isThumb(void) const {
          return this->thumb;
        }


        void Arm32Cpu::setThumb(bool state) {
          this->thumb = state;
        }

      }; /* arm32 namespace */
    }; /* arm namespace */
  }; /* arch namespace */
}; /* triton namespace */
