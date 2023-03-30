//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <algorithm>
#include <cctype>
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
    namespace arm {
      namespace aarch64 {

        AArch64Cpu::AArch64Cpu(triton::callbacks::Callbacks* callbacks) : AArch64Specifications(ARCH_AARCH64) {
          this->callbacks = callbacks;
          this->handle    = 0;

          this->clear();
          this->disassInit();
        }


        AArch64Cpu::AArch64Cpu(const AArch64Cpu& other) : AArch64Specifications(ARCH_AARCH64) {
          this->copy(other);
        }


        AArch64Cpu::~AArch64Cpu() {
          this->memory.clear();
          if (this->handle) {
            triton::extlibs::capstone::cs_close(&this->handle);
          }
        }


        void AArch64Cpu::disassInit(void) {
          if (this->handle) {
            triton::extlibs::capstone::cs_close(&this->handle);
          }

          if (triton::extlibs::capstone::cs_open(triton::extlibs::capstone::CS_ARCH_ARM64, triton::extlibs::capstone::CS_MODE_ARM, &this->handle) != triton::extlibs::capstone::CS_ERR_OK)
            throw triton::exceptions::Disassembly("AArch64Cpu::disassInit(): Cannot open capstone.");

          triton::extlibs::capstone::cs_option(this->handle, triton::extlibs::capstone::CS_OPT_DETAIL, triton::extlibs::capstone::CS_OPT_ON);
        }


        void AArch64Cpu::copy(const AArch64Cpu& other) {
          this->callbacks           = other.callbacks;
          this->exclusiveMemoryTags = other.exclusiveMemoryTags;
          this->memory              = other.memory;

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
          std::memcpy(this->q0,   other.q0,   sizeof(this->q0));
          std::memcpy(this->q1,   other.q1,   sizeof(this->q1));
          std::memcpy(this->q2,   other.q2,   sizeof(this->q2));
          std::memcpy(this->q3,   other.q3,   sizeof(this->q3));
          std::memcpy(this->q4,   other.q4,   sizeof(this->q4));
          std::memcpy(this->q5,   other.q5,   sizeof(this->q5));
          std::memcpy(this->q6,   other.q6,   sizeof(this->q6));
          std::memcpy(this->q7,   other.q7,   sizeof(this->q7));
          std::memcpy(this->q8,   other.q8,   sizeof(this->q8));
          std::memcpy(this->q9,   other.q9,   sizeof(this->q9));
          std::memcpy(this->q10,  other.q10,  sizeof(this->q10));
          std::memcpy(this->q11,  other.q11,  sizeof(this->q11));
          std::memcpy(this->q12,  other.q12,  sizeof(this->q12));
          std::memcpy(this->q13,  other.q13,  sizeof(this->q13));
          std::memcpy(this->q14,  other.q14,  sizeof(this->q14));
          std::memcpy(this->q15,  other.q15,  sizeof(this->q15));
          std::memcpy(this->q16,  other.q16,  sizeof(this->q16));
          std::memcpy(this->q17,  other.q17,  sizeof(this->q17));
          std::memcpy(this->q18,  other.q18,  sizeof(this->q18));
          std::memcpy(this->q19,  other.q19,  sizeof(this->q19));
          std::memcpy(this->q20,  other.q20,  sizeof(this->q20));
          std::memcpy(this->q21,  other.q21,  sizeof(this->q21));
          std::memcpy(this->q22,  other.q22,  sizeof(this->q22));
          std::memcpy(this->q23,  other.q23,  sizeof(this->q23));
          std::memcpy(this->q24,  other.q24,  sizeof(this->q24));
          std::memcpy(this->q25,  other.q25,  sizeof(this->q25));
          std::memcpy(this->q26,  other.q26,  sizeof(this->q26));
          std::memcpy(this->q27,  other.q27,  sizeof(this->q27));
          std::memcpy(this->q28,  other.q28,  sizeof(this->q28));
          std::memcpy(this->q29,  other.q29,  sizeof(this->q29));
          std::memcpy(this->q30,  other.q30,  sizeof(this->q30));
          std::memcpy(this->q31,  other.q31,  sizeof(this->q31));
          std::memcpy(this->sp,   other.sp,   sizeof(this->sp));
          std::memcpy(this->pc,   other.pc,   sizeof(this->pc));
          std::memcpy(this->spsr, other.spsr, sizeof(this->spsr));

          //! System registers
          #define SYS_REG_SPEC(_, LOWER_NAME, _2, _3, _4, _5) \
          std::memcpy(this->LOWER_NAME, other.LOWER_NAME, sizeof(this->LOWER_NAME));
          #define REG_SPEC(_1, _2, _3, _4, _5, _6)
          #define REG_SPEC_NO_CAPSTONE(_1, _2, _3, _4, _5, _6)
          #include "triton/aarch64.spec"
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
          std::memset(this->q0,   0x00, sizeof(this->q0));
          std::memset(this->q1,   0x00, sizeof(this->q1));
          std::memset(this->q2,   0x00, sizeof(this->q2));
          std::memset(this->q3,   0x00, sizeof(this->q3));
          std::memset(this->q4,   0x00, sizeof(this->q4));
          std::memset(this->q5,   0x00, sizeof(this->q5));
          std::memset(this->q6,   0x00, sizeof(this->q6));
          std::memset(this->q7,   0x00, sizeof(this->q7));
          std::memset(this->q8,   0x00, sizeof(this->q8));
          std::memset(this->q9,   0x00, sizeof(this->q9));
          std::memset(this->q10,  0x00, sizeof(this->q10));
          std::memset(this->q11,  0x00, sizeof(this->q11));
          std::memset(this->q12,  0x00, sizeof(this->q12));
          std::memset(this->q13,  0x00, sizeof(this->q13));
          std::memset(this->q14,  0x00, sizeof(this->q14));
          std::memset(this->q15,  0x00, sizeof(this->q15));
          std::memset(this->q16,  0x00, sizeof(this->q16));
          std::memset(this->q17,  0x00, sizeof(this->q17));
          std::memset(this->q18,  0x00, sizeof(this->q18));
          std::memset(this->q19,  0x00, sizeof(this->q19));
          std::memset(this->q20,  0x00, sizeof(this->q20));
          std::memset(this->q21,  0x00, sizeof(this->q21));
          std::memset(this->q22,  0x00, sizeof(this->q22));
          std::memset(this->q23,  0x00, sizeof(this->q23));
          std::memset(this->q24,  0x00, sizeof(this->q24));
          std::memset(this->q25,  0x00, sizeof(this->q25));
          std::memset(this->q26,  0x00, sizeof(this->q26));
          std::memset(this->q27,  0x00, sizeof(this->q27));
          std::memset(this->q28,  0x00, sizeof(this->q28));
          std::memset(this->q29,  0x00, sizeof(this->q29));
          std::memset(this->q30,  0x00, sizeof(this->q30));
          std::memset(this->q31,  0x00, sizeof(this->q31));
          std::memset(this->sp,   0x00, sizeof(this->sp));
          std::memset(this->pc,   0x00, sizeof(this->pc));
          std::memset(this->spsr, 0x00, sizeof(this->spsr));

          //! System registers
          #define SYS_REG_SPEC(_, LOWER_NAME, _2, _3, _4, _5) \
          std::memset(this->LOWER_NAME, 0x00, sizeof(this->LOWER_NAME));
          #define REG_SPEC(_1, _2, _3, _4, _5, _6)
          #define REG_SPEC_NO_CAPSTONE(_1, _2, _3, _4, _5, _6)
          #include "triton/aarch64.spec"
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
          return (this->isGPR(regId) || this->isScalarRegister(regId) || this->isVectorRegister(regId) || this->isSystemRegister(regId));
        }


        bool AArch64Cpu::isRegisterValid(triton::arch::register_e regId) const {
          return (this->isFlag(regId) || this->isRegister(regId));
        }


        bool AArch64Cpu::isGPR(triton::arch::register_e regId) const {
          return ((regId >= triton::arch::ID_REG_AARCH64_X0 && regId <= triton::arch::ID_REG_AARCH64_WZR) ? true : false);
        }


        bool AArch64Cpu::isScalarRegister(triton::arch::register_e regId) const {
          return ((regId >= triton::arch::ID_REG_AARCH64_Q0 && regId <= triton::arch::ID_REG_AARCH64_B31) ? true : false);
        }


        bool AArch64Cpu::isVectorRegister(triton::arch::register_e regId) const {
          return ((regId >= triton::arch::ID_REG_AARCH64_V0 && regId <= triton::arch::ID_REG_AARCH64_V31) ? true : false);
        }


        bool AArch64Cpu::isSystemRegister(triton::arch::register_e regId) const {
          return ((regId >= triton::arch::ID_REG_AARCH64_ACTLR_EL1 && regId <= triton::arch::ID_REG_AARCH64_ZCR_EL3) ? true : false);
        }


        triton::uint32 AArch64Cpu::numberOfRegisters(void) const {
          return triton::arch::ID_REG_LAST_ITEM;
        }


        triton::uint32 AArch64Cpu::gprSize(void) const {
          return triton::size::qword;
        }


        triton::uint32 AArch64Cpu::gprBitSize(void) const {
          return triton::bitsize::qword;
        }


        const std::unordered_map<triton::arch::register_e, const triton::arch::Register>& AArch64Cpu::getAllRegisters(void) const {
          return this->id2reg;
        }

        const std::unordered_map<triton::uint64, triton::uint8, IdentityHash<triton::uint64>>& AArch64Cpu::getConcreteMemory(void) const {
          return this->memory;
        }


        std::set<const triton::arch::Register*> AArch64Cpu::getParentRegisters(void) const {
          std::set<const triton::arch::Register*> ret;

          for (const auto& kv: this->id2reg) {
            auto regId = kv.first;
            const auto& reg = kv.second;

            /* Skip Vector and System registers */
            if (this->isVectorRegister(regId) || this->isSystemRegister(regId))
              continue;

            /* Add GPR */
            if (reg.getSize() == this->gprSize())
              ret.insert(&reg);

            /* Add scalar register */
            if (this->isScalarRegister(regId) && reg.getSize() == triton::bitsize::dqword)
              ret.insert(&reg);

            /* Add Flags */
            else if (this->isFlag(regId))
              ret.insert(&reg);
          }

          return ret;
        }


        const triton::arch::Register& AArch64Cpu::getRegister(triton::arch::register_e id) const {
          try {
            return this->id2reg.at(id);
          } catch (const std::out_of_range&) {
            throw triton::exceptions::Cpu("AArch64Cpu::getRegister(): Invalid register for this architecture.");
          }
        }


        const triton::arch::Register& AArch64Cpu::getRegister(const std::string& name) const {
        std::string lower = name;
        std::transform(lower.begin(), lower.end(), lower.begin(), [](unsigned char c){ return std::tolower(c); });
          try {
            return this->getRegister(this->name2id.at(lower));
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


        void AArch64Cpu::disassembly(triton::arch::Instruction& inst) {
          triton::extlibs::capstone::cs_insn* insn;
          triton::usize count = 0;
          triton::uint32 size = 0;

          /* Check if the opcode and opcode' size are defined */
          if (inst.getOpcode() == nullptr || inst.getSize() == 0)
            throw triton::exceptions::Disassembly("AArch64Cpu::disassembly(): Opcode and opcodeSize must be definied.");

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
            if (detail->arm64.op_count)
              str << " " <<  insn[0].op_str;

            inst.setDisassembly(str.str());

            /* Refine the size */
            inst.setSize(insn[0].size);

            /* Init the instruction's type */
            inst.setType(this->capstoneInstructionToTritonInstruction(insn[0].id));

            /* Init the instruction's code codition */
            inst.setCodeCondition(this->capstoneConditionToTritonCondition(detail->arm64.cc));

            /* Init the instruction's write back flag */
            inst.setWriteBack(detail->arm64.writeback);

            /* Set True if the instruction udpate flags */
            inst.setUpdateFlag(detail->arm64.update_flags);

            /* Set architecture */
            inst.setArchitecture(triton::arch::ARCH_AARCH64);

            /* Init operands */
            for (triton::uint32 n = 0; n < detail->arm64.op_count; n++) {
              triton::extlibs::capstone::cs_arm64_op* op = &(detail->arm64.operands[n]);
              switch(op->type) {

                case triton::extlibs::capstone::ARM64_OP_IMM: {
                  triton::arch::Immediate imm(op->imm, size ? size : triton::size::qword);

                  /*
                   * Instruction such that CBZ, CBNZ or TBZ may imply a wrong size.
                   * So, if Triton truncates the value by setting a size less than
                   * the original one, we redefine the size automatically.
                   */
                  if (static_cast<triton::uint64>(op->imm) > imm.getValue()) {
                    imm = Immediate();
                    imm.setValue(op->imm, 0); /* By setting 0 as size, we automatically identify the size of the value */
                  }

                  /* Set Shift type and value */
                  imm.setShiftType(this->capstoneShiftToTritonShift(op->shift.type));
                  imm.setShiftValue(op->shift.value);

                  inst.operands.push_back(triton::arch::OperandWrapper(imm));
                  break;
                }

                case triton::extlibs::capstone::ARM64_OP_MEM: {
                  triton::arch::MemoryAccess mem;

                  /* Set the size of the memory access */
                  mem.setBits(size ? ((size * triton::bitsize::byte) - 1) : triton::bitsize::qword - 1, 0);

                  /* LEA if exists */
                  triton::arch::Register base(*this, this->capstoneRegisterToTritonRegister(op->mem.base));
                  triton::arch::Register index(*this, this->capstoneRegisterToTritonRegister(op->mem.index));

                  triton::uint32 immsize = (
                    this->isRegisterValid(base.getId()) ? base.getSize() :
                    this->isRegisterValid(index.getId()) ? index.getSize() :
                    this->gprSize()
                  );

                  triton::arch::Immediate disp(op->mem.disp, immsize);

                  /* Specify that LEA contains a PC relative */
                  if (base.getId() == this->pcId) {
                    mem.setPcRelative(inst.getNextAddress());
                  }

                  /* Set Shift type and value */
                  index.setShiftType(this->capstoneShiftToTritonShift(op->shift.type));
                  index.setShiftValue(op->shift.value);

                  /* Set extend type and size */
                  index.setExtendType(this->capstoneExtendToTritonExtend(op->ext));
                  if (op->ext != triton::extlibs::capstone::ARM64_EXT_INVALID) {
                    index.setExtendedSize(base.getBitSize());
                  }

                  /* Note that in ARM64 there is no segment register and scale value */
                  mem.setBaseRegister(base);
                  mem.setIndexRegister(index);
                  mem.setDisplacement(disp);

                  /* If there is an index register available, set scale to 1 to perform this following computation (base) + (index * scale) */
                  if (this->isRegisterValid(index.getId())) {
                    mem.setScale(triton::arch::Immediate(1, immsize));
                  }

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
                  if (op->ext != triton::extlibs::capstone::ARM64_EXT_INVALID) {
                    reg.setExtendedSize(size * triton::bitsize::byte);
                  }

                  /* Init the vector arrangement specifier */
                  reg.setVASType(this->capstoneVASToTritonVAS(op->vas));

                  /* Init the vector index (-1 if irrelevant) */
                  reg.setVectorIndex(op->vector_index);

                  /* Define a base address for next operand */
                  size = this->getMemoryOperandSpecialSize(inst.getType());
                  if (!size) {
                    size = reg.getSize();
                  }

                  inst.operands.push_back(triton::arch::OperandWrapper(reg));
                  break;
                }

                case triton::extlibs::capstone::ARM64_OP_SYS: {
                  triton::arch::Register reg(*this, this->capstoneRegisterToTritonRegister(op->reg));

                  /* Define a base address for next operand */
                  size = this->getMemoryOperandSpecialSize(inst.getType());
                  if (!size) {
                    size = reg.getSize();
                  }

                  inst.operands.push_back(triton::arch::OperandWrapper(reg));
                  break;
                }

                default:
                  /* NOTE: FP, CIMM, and missing one are not supported yet. */
                  throw triton::exceptions::Disassembly("AArch64Cpu::disassembly(): Invalid operand.");
              } // switch
            } // for operand

            /* Set control flow */
            if (insn[0].id == triton::extlibs::capstone::ARM64_INS_RET)
              inst.setControlFlow(true);

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
        }


        triton::uint8 AArch64Cpu::getConcreteMemoryValue(triton::uint64 addr, bool execCallbacks) const {
          if (execCallbacks && this->callbacks)
            this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, triton::size::byte));

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

          if (size == 0 || size > triton::size::dqqword)
            throw triton::exceptions::Cpu("AArch64Cpu::getConcreteMemoryValue(): Invalid size memory.");

          for (triton::sint32 i = size-1; i >= 0; i--)
            ret = ((ret << triton::bitsize::byte) | this->getConcreteMemoryValue(addr+i, false));

          return ret;
        }


        std::vector<triton::uint8> AArch64Cpu::getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks) const {
          std::vector<triton::uint8> area;

          for (triton::usize index = 0; index < size; index++)
            area.push_back(this->getConcreteMemoryValue(baseAddr+index, execCallbacks));

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
            case triton::arch::ID_REG_AARCH64_Q0:   return triton::utils::cast<triton::uint128>(this->q0);
            case triton::arch::ID_REG_AARCH64_D0:   return (*((triton::uint64*)(this->q0)));
            case triton::arch::ID_REG_AARCH64_S0:   return (*((triton::uint32*)(this->q0)));
            case triton::arch::ID_REG_AARCH64_H0:   return (*((triton::uint16*)(this->q0)));
            case triton::arch::ID_REG_AARCH64_B0:   return (*((triton::uint8*)(this->q0)));
            case triton::arch::ID_REG_AARCH64_Q1:   return triton::utils::cast<triton::uint128>(this->q1);
            case triton::arch::ID_REG_AARCH64_D1:   return (*((triton::uint64*)(this->q1)));
            case triton::arch::ID_REG_AARCH64_S1:   return (*((triton::uint32*)(this->q1)));
            case triton::arch::ID_REG_AARCH64_H1:   return (*((triton::uint16*)(this->q1)));
            case triton::arch::ID_REG_AARCH64_B1:   return (*((triton::uint8*)(this->q1)));
            case triton::arch::ID_REG_AARCH64_Q2:   return triton::utils::cast<triton::uint128>(this->q2);
            case triton::arch::ID_REG_AARCH64_D2:   return (*((triton::uint64*)(this->q2)));
            case triton::arch::ID_REG_AARCH64_S2:   return (*((triton::uint32*)(this->q2)));
            case triton::arch::ID_REG_AARCH64_H2:   return (*((triton::uint16*)(this->q2)));
            case triton::arch::ID_REG_AARCH64_B2:   return (*((triton::uint8*)(this->q2)));
            case triton::arch::ID_REG_AARCH64_Q3:   return triton::utils::cast<triton::uint128>(this->q3);
            case triton::arch::ID_REG_AARCH64_D3:   return (*((triton::uint64*)(this->q3)));
            case triton::arch::ID_REG_AARCH64_S3:   return (*((triton::uint32*)(this->q3)));
            case triton::arch::ID_REG_AARCH64_H3:   return (*((triton::uint16*)(this->q3)));
            case triton::arch::ID_REG_AARCH64_B3:   return (*((triton::uint8*)(this->q3)));
            case triton::arch::ID_REG_AARCH64_Q4:   return triton::utils::cast<triton::uint128>(this->q4);
            case triton::arch::ID_REG_AARCH64_D4:   return (*((triton::uint64*)(this->q4)));
            case triton::arch::ID_REG_AARCH64_S4:   return (*((triton::uint32*)(this->q4)));
            case triton::arch::ID_REG_AARCH64_H4:   return (*((triton::uint16*)(this->q4)));
            case triton::arch::ID_REG_AARCH64_B4:   return (*((triton::uint8*)(this->q4)));
            case triton::arch::ID_REG_AARCH64_Q5:   return triton::utils::cast<triton::uint128>(this->q5);
            case triton::arch::ID_REG_AARCH64_D5:   return (*((triton::uint64*)(this->q5)));
            case triton::arch::ID_REG_AARCH64_S5:   return (*((triton::uint32*)(this->q5)));
            case triton::arch::ID_REG_AARCH64_H5:   return (*((triton::uint16*)(this->q5)));
            case triton::arch::ID_REG_AARCH64_B5:   return (*((triton::uint8*)(this->q5)));
            case triton::arch::ID_REG_AARCH64_Q6:   return triton::utils::cast<triton::uint128>(this->q6);
            case triton::arch::ID_REG_AARCH64_D6:   return (*((triton::uint64*)(this->q6)));
            case triton::arch::ID_REG_AARCH64_S6:   return (*((triton::uint32*)(this->q6)));
            case triton::arch::ID_REG_AARCH64_H6:   return (*((triton::uint16*)(this->q6)));
            case triton::arch::ID_REG_AARCH64_B6:   return (*((triton::uint8*)(this->q6)));
            case triton::arch::ID_REG_AARCH64_Q7:   return triton::utils::cast<triton::uint128>(this->q7);
            case triton::arch::ID_REG_AARCH64_D7:   return (*((triton::uint64*)(this->q7)));
            case triton::arch::ID_REG_AARCH64_S7:   return (*((triton::uint32*)(this->q7)));
            case triton::arch::ID_REG_AARCH64_H7:   return (*((triton::uint16*)(this->q7)));
            case triton::arch::ID_REG_AARCH64_B7:   return (*((triton::uint8*)(this->q7)));
            case triton::arch::ID_REG_AARCH64_Q8:   return triton::utils::cast<triton::uint128>(this->q8);
            case triton::arch::ID_REG_AARCH64_D8:   return (*((triton::uint64*)(this->q8)));
            case triton::arch::ID_REG_AARCH64_S8:   return (*((triton::uint32*)(this->q8)));
            case triton::arch::ID_REG_AARCH64_H8:   return (*((triton::uint16*)(this->q8)));
            case triton::arch::ID_REG_AARCH64_B8:   return (*((triton::uint8*)(this->q8)));
            case triton::arch::ID_REG_AARCH64_Q9:   return triton::utils::cast<triton::uint128>(this->q9);
            case triton::arch::ID_REG_AARCH64_D9:   return (*((triton::uint64*)(this->q9)));
            case triton::arch::ID_REG_AARCH64_S9:   return (*((triton::uint32*)(this->q9)));
            case triton::arch::ID_REG_AARCH64_H9:   return (*((triton::uint16*)(this->q9)));
            case triton::arch::ID_REG_AARCH64_B9:   return (*((triton::uint8*)(this->q9)));
            case triton::arch::ID_REG_AARCH64_Q10:  return triton::utils::cast<triton::uint128>(this->q10);
            case triton::arch::ID_REG_AARCH64_D10:  return (*((triton::uint64*)(this->q10)));
            case triton::arch::ID_REG_AARCH64_S10:  return (*((triton::uint32*)(this->q10)));
            case triton::arch::ID_REG_AARCH64_H10:  return (*((triton::uint16*)(this->q10)));
            case triton::arch::ID_REG_AARCH64_B10:  return (*((triton::uint8*)(this->q10)));
            case triton::arch::ID_REG_AARCH64_Q11:  return triton::utils::cast<triton::uint128>(this->q11);
            case triton::arch::ID_REG_AARCH64_D11:  return (*((triton::uint64*)(this->q11)));
            case triton::arch::ID_REG_AARCH64_S11:  return (*((triton::uint32*)(this->q11)));
            case triton::arch::ID_REG_AARCH64_H11:  return (*((triton::uint16*)(this->q11)));
            case triton::arch::ID_REG_AARCH64_B11:  return (*((triton::uint8*)(this->q11)));
            case triton::arch::ID_REG_AARCH64_Q12:  return triton::utils::cast<triton::uint128>(this->q12);
            case triton::arch::ID_REG_AARCH64_D12:  return (*((triton::uint64*)(this->q12)));
            case triton::arch::ID_REG_AARCH64_S12:  return (*((triton::uint32*)(this->q12)));
            case triton::arch::ID_REG_AARCH64_H12:  return (*((triton::uint16*)(this->q12)));
            case triton::arch::ID_REG_AARCH64_B12:  return (*((triton::uint8*)(this->q12)));
            case triton::arch::ID_REG_AARCH64_Q13:  return triton::utils::cast<triton::uint128>(this->q13);
            case triton::arch::ID_REG_AARCH64_D13:  return (*((triton::uint64*)(this->q13)));
            case triton::arch::ID_REG_AARCH64_S13:  return (*((triton::uint32*)(this->q13)));
            case triton::arch::ID_REG_AARCH64_H13:  return (*((triton::uint16*)(this->q13)));
            case triton::arch::ID_REG_AARCH64_B13:  return (*((triton::uint8*)(this->q13)));
            case triton::arch::ID_REG_AARCH64_Q14:  return triton::utils::cast<triton::uint128>(this->q14);
            case triton::arch::ID_REG_AARCH64_D14:  return (*((triton::uint64*)(this->q14)));
            case triton::arch::ID_REG_AARCH64_S14:  return (*((triton::uint32*)(this->q14)));
            case triton::arch::ID_REG_AARCH64_H14:  return (*((triton::uint16*)(this->q14)));
            case triton::arch::ID_REG_AARCH64_B14:  return (*((triton::uint8*)(this->q14)));
            case triton::arch::ID_REG_AARCH64_Q15:  return triton::utils::cast<triton::uint128>(this->q15);
            case triton::arch::ID_REG_AARCH64_D15:  return (*((triton::uint64*)(this->q15)));
            case triton::arch::ID_REG_AARCH64_S15:  return (*((triton::uint32*)(this->q15)));
            case triton::arch::ID_REG_AARCH64_H15:  return (*((triton::uint16*)(this->q15)));
            case triton::arch::ID_REG_AARCH64_B15:  return (*((triton::uint8*)(this->q15)));
            case triton::arch::ID_REG_AARCH64_Q16:  return triton::utils::cast<triton::uint128>(this->q16);
            case triton::arch::ID_REG_AARCH64_D16:  return (*((triton::uint64*)(this->q16)));
            case triton::arch::ID_REG_AARCH64_S16:  return (*((triton::uint32*)(this->q16)));
            case triton::arch::ID_REG_AARCH64_H16:  return (*((triton::uint16*)(this->q16)));
            case triton::arch::ID_REG_AARCH64_B16:  return (*((triton::uint8*)(this->q16)));
            case triton::arch::ID_REG_AARCH64_Q17:  return triton::utils::cast<triton::uint128>(this->q17);
            case triton::arch::ID_REG_AARCH64_D17:  return (*((triton::uint64*)(this->q17)));
            case triton::arch::ID_REG_AARCH64_S17:  return (*((triton::uint32*)(this->q17)));
            case triton::arch::ID_REG_AARCH64_H17:  return (*((triton::uint16*)(this->q17)));
            case triton::arch::ID_REG_AARCH64_B17:  return (*((triton::uint8*)(this->q17)));
            case triton::arch::ID_REG_AARCH64_Q18:  return triton::utils::cast<triton::uint128>(this->q18);
            case triton::arch::ID_REG_AARCH64_D18:  return (*((triton::uint64*)(this->q18)));
            case triton::arch::ID_REG_AARCH64_S18:  return (*((triton::uint32*)(this->q18)));
            case triton::arch::ID_REG_AARCH64_H18:  return (*((triton::uint16*)(this->q18)));
            case triton::arch::ID_REG_AARCH64_B18:  return (*((triton::uint8*)(this->q18)));
            case triton::arch::ID_REG_AARCH64_Q19:  return triton::utils::cast<triton::uint128>(this->q19);
            case triton::arch::ID_REG_AARCH64_D19:  return (*((triton::uint64*)(this->q19)));
            case triton::arch::ID_REG_AARCH64_S19:  return (*((triton::uint32*)(this->q19)));
            case triton::arch::ID_REG_AARCH64_H19:  return (*((triton::uint16*)(this->q19)));
            case triton::arch::ID_REG_AARCH64_B19:  return (*((triton::uint8*)(this->q19)));
            case triton::arch::ID_REG_AARCH64_Q20:  return triton::utils::cast<triton::uint128>(this->q20);
            case triton::arch::ID_REG_AARCH64_D20:  return (*((triton::uint64*)(this->q20)));
            case triton::arch::ID_REG_AARCH64_S20:  return (*((triton::uint32*)(this->q20)));
            case triton::arch::ID_REG_AARCH64_H20:  return (*((triton::uint16*)(this->q20)));
            case triton::arch::ID_REG_AARCH64_B20:  return (*((triton::uint8*)(this->q20)));
            case triton::arch::ID_REG_AARCH64_Q21:  return triton::utils::cast<triton::uint128>(this->q21);
            case triton::arch::ID_REG_AARCH64_D21:  return (*((triton::uint64*)(this->q21)));
            case triton::arch::ID_REG_AARCH64_S21:  return (*((triton::uint32*)(this->q21)));
            case triton::arch::ID_REG_AARCH64_H21:  return (*((triton::uint16*)(this->q21)));
            case triton::arch::ID_REG_AARCH64_B21:  return (*((triton::uint8*)(this->q21)));
            case triton::arch::ID_REG_AARCH64_Q22:  return triton::utils::cast<triton::uint128>(this->q22);
            case triton::arch::ID_REG_AARCH64_D22:  return (*((triton::uint64*)(this->q22)));
            case triton::arch::ID_REG_AARCH64_S22:  return (*((triton::uint32*)(this->q22)));
            case triton::arch::ID_REG_AARCH64_H22:  return (*((triton::uint16*)(this->q22)));
            case triton::arch::ID_REG_AARCH64_B22:  return (*((triton::uint8*)(this->q22)));
            case triton::arch::ID_REG_AARCH64_Q23:  return triton::utils::cast<triton::uint128>(this->q23);
            case triton::arch::ID_REG_AARCH64_D23:  return (*((triton::uint64*)(this->q23)));
            case triton::arch::ID_REG_AARCH64_S23:  return (*((triton::uint32*)(this->q23)));
            case triton::arch::ID_REG_AARCH64_H23:  return (*((triton::uint16*)(this->q23)));
            case triton::arch::ID_REG_AARCH64_B23:  return (*((triton::uint8*)(this->q23)));
            case triton::arch::ID_REG_AARCH64_Q24:  return triton::utils::cast<triton::uint128>(this->q24);
            case triton::arch::ID_REG_AARCH64_D24:  return (*((triton::uint64*)(this->q24)));
            case triton::arch::ID_REG_AARCH64_S24:  return (*((triton::uint32*)(this->q24)));
            case triton::arch::ID_REG_AARCH64_H24:  return (*((triton::uint16*)(this->q24)));
            case triton::arch::ID_REG_AARCH64_B24:  return (*((triton::uint8*)(this->q24)));
            case triton::arch::ID_REG_AARCH64_Q25:  return triton::utils::cast<triton::uint128>(this->q25);
            case triton::arch::ID_REG_AARCH64_D25:  return (*((triton::uint64*)(this->q25)));
            case triton::arch::ID_REG_AARCH64_S25:  return (*((triton::uint32*)(this->q25)));
            case triton::arch::ID_REG_AARCH64_H25:  return (*((triton::uint16*)(this->q25)));
            case triton::arch::ID_REG_AARCH64_B25:  return (*((triton::uint8*)(this->q25)));
            case triton::arch::ID_REG_AARCH64_Q26:  return triton::utils::cast<triton::uint128>(this->q26);
            case triton::arch::ID_REG_AARCH64_D26:  return (*((triton::uint64*)(this->q26)));
            case triton::arch::ID_REG_AARCH64_S26:  return (*((triton::uint32*)(this->q26)));
            case triton::arch::ID_REG_AARCH64_H26:  return (*((triton::uint16*)(this->q26)));
            case triton::arch::ID_REG_AARCH64_B26:  return (*((triton::uint8*)(this->q26)));
            case triton::arch::ID_REG_AARCH64_Q27:  return triton::utils::cast<triton::uint128>(this->q27);
            case triton::arch::ID_REG_AARCH64_D27:  return (*((triton::uint64*)(this->q27)));
            case triton::arch::ID_REG_AARCH64_S27:  return (*((triton::uint32*)(this->q27)));
            case triton::arch::ID_REG_AARCH64_H27:  return (*((triton::uint16*)(this->q27)));
            case triton::arch::ID_REG_AARCH64_B27:  return (*((triton::uint8*)(this->q27)));
            case triton::arch::ID_REG_AARCH64_Q28:  return triton::utils::cast<triton::uint128>(this->q28);
            case triton::arch::ID_REG_AARCH64_D28:  return (*((triton::uint64*)(this->q28)));
            case triton::arch::ID_REG_AARCH64_S28:  return (*((triton::uint32*)(this->q28)));
            case triton::arch::ID_REG_AARCH64_H28:  return (*((triton::uint16*)(this->q28)));
            case triton::arch::ID_REG_AARCH64_B28:  return (*((triton::uint8*)(this->q28)));
            case triton::arch::ID_REG_AARCH64_Q29:  return triton::utils::cast<triton::uint128>(this->q29);
            case triton::arch::ID_REG_AARCH64_D29:  return (*((triton::uint64*)(this->q29)));
            case triton::arch::ID_REG_AARCH64_S29:  return (*((triton::uint32*)(this->q29)));
            case triton::arch::ID_REG_AARCH64_H29:  return (*((triton::uint16*)(this->q29)));
            case triton::arch::ID_REG_AARCH64_B29:  return (*((triton::uint8*)(this->q29)));
            case triton::arch::ID_REG_AARCH64_Q30:  return triton::utils::cast<triton::uint128>(this->q30);
            case triton::arch::ID_REG_AARCH64_D30:  return (*((triton::uint64*)(this->q30)));
            case triton::arch::ID_REG_AARCH64_S30:  return (*((triton::uint32*)(this->q30)));
            case triton::arch::ID_REG_AARCH64_H30:  return (*((triton::uint16*)(this->q30)));
            case triton::arch::ID_REG_AARCH64_B30:  return (*((triton::uint8*)(this->q30)));
            case triton::arch::ID_REG_AARCH64_Q31:  return triton::utils::cast<triton::uint128>(this->q31);
            case triton::arch::ID_REG_AARCH64_D31:  return (*((triton::uint64*)(this->q31)));
            case triton::arch::ID_REG_AARCH64_S31:  return (*((triton::uint32*)(this->q31)));
            case triton::arch::ID_REG_AARCH64_H31:  return (*((triton::uint16*)(this->q31)));
            case triton::arch::ID_REG_AARCH64_B31:  return (*((triton::uint8*)(this->q31)));
            case triton::arch::ID_REG_AARCH64_V0:   return triton::utils::cast<triton::uint128>(this->q0);
            case triton::arch::ID_REG_AARCH64_V1:   return triton::utils::cast<triton::uint128>(this->q1);
            case triton::arch::ID_REG_AARCH64_V2:   return triton::utils::cast<triton::uint128>(this->q2);
            case triton::arch::ID_REG_AARCH64_V3:   return triton::utils::cast<triton::uint128>(this->q3);
            case triton::arch::ID_REG_AARCH64_V4:   return triton::utils::cast<triton::uint128>(this->q4);
            case triton::arch::ID_REG_AARCH64_V5:   return triton::utils::cast<triton::uint128>(this->q5);
            case triton::arch::ID_REG_AARCH64_V6:   return triton::utils::cast<triton::uint128>(this->q6);
            case triton::arch::ID_REG_AARCH64_V7:   return triton::utils::cast<triton::uint128>(this->q7);
            case triton::arch::ID_REG_AARCH64_V8:   return triton::utils::cast<triton::uint128>(this->q8);
            case triton::arch::ID_REG_AARCH64_V9:   return triton::utils::cast<triton::uint128>(this->q9);
            case triton::arch::ID_REG_AARCH64_V10:  return triton::utils::cast<triton::uint128>(this->q10);
            case triton::arch::ID_REG_AARCH64_V11:  return triton::utils::cast<triton::uint128>(this->q11);
            case triton::arch::ID_REG_AARCH64_V12:  return triton::utils::cast<triton::uint128>(this->q12);
            case triton::arch::ID_REG_AARCH64_V13:  return triton::utils::cast<triton::uint128>(this->q13);
            case triton::arch::ID_REG_AARCH64_V14:  return triton::utils::cast<triton::uint128>(this->q14);
            case triton::arch::ID_REG_AARCH64_V15:  return triton::utils::cast<triton::uint128>(this->q15);
            case triton::arch::ID_REG_AARCH64_V16:  return triton::utils::cast<triton::uint128>(this->q16);
            case triton::arch::ID_REG_AARCH64_V17:  return triton::utils::cast<triton::uint128>(this->q17);
            case triton::arch::ID_REG_AARCH64_V18:  return triton::utils::cast<triton::uint128>(this->q18);
            case triton::arch::ID_REG_AARCH64_V19:  return triton::utils::cast<triton::uint128>(this->q19);
            case triton::arch::ID_REG_AARCH64_V20:  return triton::utils::cast<triton::uint128>(this->q20);
            case triton::arch::ID_REG_AARCH64_V21:  return triton::utils::cast<triton::uint128>(this->q21);
            case triton::arch::ID_REG_AARCH64_V22:  return triton::utils::cast<triton::uint128>(this->q22);
            case triton::arch::ID_REG_AARCH64_V23:  return triton::utils::cast<triton::uint128>(this->q23);
            case triton::arch::ID_REG_AARCH64_V24:  return triton::utils::cast<triton::uint128>(this->q24);
            case triton::arch::ID_REG_AARCH64_V25:  return triton::utils::cast<triton::uint128>(this->q25);
            case triton::arch::ID_REG_AARCH64_V26:  return triton::utils::cast<triton::uint128>(this->q26);
            case triton::arch::ID_REG_AARCH64_V27:  return triton::utils::cast<triton::uint128>(this->q27);
            case triton::arch::ID_REG_AARCH64_V28:  return triton::utils::cast<triton::uint128>(this->q28);
            case triton::arch::ID_REG_AARCH64_V29:  return triton::utils::cast<triton::uint128>(this->q29);
            case triton::arch::ID_REG_AARCH64_V30:  return triton::utils::cast<triton::uint128>(this->q30);
            case triton::arch::ID_REG_AARCH64_V31:  return triton::utils::cast<triton::uint128>(this->q31);

            //! System registers
            #define SYS_REG_SPEC(UPPER_NAME, LOWER_NAME, _2, _3, _4, _5) \
            case triton::arch::ID_REG_AARCH64_##UPPER_NAME: return (*((triton::uint64*)(this->LOWER_NAME)));
            #define REG_SPEC(_1, _2, _3, _4, _5, _6)
            #define REG_SPEC_NO_CAPSTONE(_1, _2, _3, _4, _5, _6)
            #include "triton/aarch64.spec"

            default:
              throw triton::exceptions::Cpu("AArch64Cpu::getConcreteRegisterValue(): Invalid register.");
          }

          return value;
        }


        void AArch64Cpu::setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value, bool execCallbacks) {
          if (execCallbacks && this->callbacks)
            this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, triton::size::byte), value);
          this->memory[addr] = value;
        }


        void AArch64Cpu::setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value, bool execCallbacks) {
          triton::uint64 addr = mem.getAddress();
          triton::uint32 size = mem.getSize();
          triton::uint512 cv  = value;

          if (cv > mem.getMaxValue())
            throw triton::exceptions::Register("AArch64Cpu::setConcreteMemoryValue(): You cannot set this concrete value (too big) to this memory access.");

          if (size == 0 || size > triton::size::dqqword)
            throw triton::exceptions::Cpu("AArch64Cpu::setConcreteMemoryValue(): Invalid size memory.");

          if (execCallbacks && this->callbacks)
            this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, mem, value);

          for (triton::uint32 i = 0; i < size; i++) {
            this->memory[addr+i] = static_cast<triton::uint8>((cv & 0xff));
            cv >>= 8;
          }
        }


        void AArch64Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values, bool execCallbacks) {
          this->memory.reserve(values.size() + this->memory.size());
          for (triton::usize index = 0; index < values.size(); index++) {
            this->setConcreteMemoryValue(baseAddr+index, values[index], execCallbacks);
          }
        }


        void AArch64Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const void* area, triton::usize size, bool execCallbacks) {
          this->memory.reserve(size + this->memory.size());
          for (triton::usize index = 0; index < size; index++) {
            this->setConcreteMemoryValue(baseAddr+index, reinterpret_cast<const triton::uint8*>(area)[index], execCallbacks);
          }
        }


        void AArch64Cpu::setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value, bool execCallbacks) {
          if (value > reg.getMaxValue())
            throw triton::exceptions::Register("AArch64Cpu::setConcreteRegisterValue(): You cannot set this concrete value (too big) to this register.");

          if (execCallbacks && this->callbacks)
            this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_REGISTER_VALUE, reg, value);

          switch (reg.getId()) {
            case triton::arch::ID_REG_AARCH64_X0:   (*((triton::uint64*)(this->x0)))   = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W0:   (*((triton::uint32*)(this->x0)))   = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X1:   (*((triton::uint64*)(this->x1)))   = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W1:   (*((triton::uint32*)(this->x1)))   = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X2:   (*((triton::uint64*)(this->x2)))   = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W2:   (*((triton::uint32*)(this->x2)))   = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X3:   (*((triton::uint64*)(this->x3)))   = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W3:   (*((triton::uint32*)(this->x3)))   = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X4:   (*((triton::uint64*)(this->x4)))   = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W4:   (*((triton::uint32*)(this->x4)))   = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X5:   (*((triton::uint64*)(this->x5)))   = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W5:   (*((triton::uint32*)(this->x5)))   = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X6:   (*((triton::uint64*)(this->x6)))   = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W6:   (*((triton::uint32*)(this->x6)))   = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X7:   (*((triton::uint64*)(this->x7)))   = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W7:   (*((triton::uint32*)(this->x7)))   = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X8:   (*((triton::uint64*)(this->x8)))   = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W8:   (*((triton::uint32*)(this->x8)))   = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X9:   (*((triton::uint64*)(this->x9)))   = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W9:   (*((triton::uint32*)(this->x9)))   = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X10:  (*((triton::uint64*)(this->x10)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W10:  (*((triton::uint32*)(this->x10)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X11:  (*((triton::uint64*)(this->x11)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W11:  (*((triton::uint32*)(this->x11)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X12:  (*((triton::uint64*)(this->x12)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W12:  (*((triton::uint32*)(this->x12)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X13:  (*((triton::uint64*)(this->x13)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W13:  (*((triton::uint32*)(this->x13)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X14:  (*((triton::uint64*)(this->x14)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W14:  (*((triton::uint32*)(this->x14)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X15:  (*((triton::uint64*)(this->x15)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W15:  (*((triton::uint32*)(this->x15)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X16:  (*((triton::uint64*)(this->x16)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W16:  (*((triton::uint32*)(this->x16)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X17:  (*((triton::uint64*)(this->x17)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W17:  (*((triton::uint32*)(this->x17)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X18:  (*((triton::uint64*)(this->x18)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W18:  (*((triton::uint32*)(this->x18)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X19:  (*((triton::uint64*)(this->x19)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W19:  (*((triton::uint32*)(this->x19)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X20:  (*((triton::uint64*)(this->x20)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W20:  (*((triton::uint32*)(this->x20)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X21:  (*((triton::uint64*)(this->x21)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W21:  (*((triton::uint32*)(this->x21)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X22:  (*((triton::uint64*)(this->x22)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W22:  (*((triton::uint32*)(this->x22)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X23:  (*((triton::uint64*)(this->x23)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W23:  (*((triton::uint32*)(this->x23)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X24:  (*((triton::uint64*)(this->x24)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W24:  (*((triton::uint32*)(this->x24)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X25:  (*((triton::uint64*)(this->x25)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W25:  (*((triton::uint32*)(this->x25)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X26:  (*((triton::uint64*)(this->x26)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W26:  (*((triton::uint32*)(this->x26)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X27:  (*((triton::uint64*)(this->x27)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W27:  (*((triton::uint32*)(this->x27)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X28:  (*((triton::uint64*)(this->x28)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W28:  (*((triton::uint32*)(this->x28)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X29:  (*((triton::uint64*)(this->x29)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W29:  (*((triton::uint32*)(this->x29)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_X30:  (*((triton::uint64*)(this->x30)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_W30:  (*((triton::uint32*)(this->x30)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_SP:   (*((triton::uint64*)(this->sp)))   = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_WSP:  (*((triton::uint32*)(this->sp)))   = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_PC:   (*((triton::uint64*)(this->pc)))   = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_SPSR: (*((triton::uint32*)(this->spsr))) = static_cast<triton::uint32>(value); break;

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
            case triton::arch::ID_REG_AARCH64_Q0:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q0);  break;
            case triton::arch::ID_REG_AARCH64_Q1:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q1);  break;
            case triton::arch::ID_REG_AARCH64_Q2:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q2);  break;
            case triton::arch::ID_REG_AARCH64_Q3:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q3);  break;
            case triton::arch::ID_REG_AARCH64_Q4:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q4);  break;
            case triton::arch::ID_REG_AARCH64_Q5:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q5);  break;
            case triton::arch::ID_REG_AARCH64_Q6:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q6);  break;
            case triton::arch::ID_REG_AARCH64_Q7:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q7);  break;
            case triton::arch::ID_REG_AARCH64_Q8:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q8);  break;
            case triton::arch::ID_REG_AARCH64_Q9:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q9);  break;
            case triton::arch::ID_REG_AARCH64_Q10: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q10); break;
            case triton::arch::ID_REG_AARCH64_Q11: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q11); break;
            case triton::arch::ID_REG_AARCH64_Q12: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q12); break;
            case triton::arch::ID_REG_AARCH64_Q13: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q13); break;
            case triton::arch::ID_REG_AARCH64_Q14: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q14); break;
            case triton::arch::ID_REG_AARCH64_Q15: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q15); break;
            case triton::arch::ID_REG_AARCH64_Q16: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q16); break;
            case triton::arch::ID_REG_AARCH64_Q17: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q17); break;
            case triton::arch::ID_REG_AARCH64_Q18: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q18); break;
            case triton::arch::ID_REG_AARCH64_Q19: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q19); break;
            case triton::arch::ID_REG_AARCH64_Q20: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q20); break;
            case triton::arch::ID_REG_AARCH64_Q21: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q21); break;
            case triton::arch::ID_REG_AARCH64_Q22: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q22); break;
            case triton::arch::ID_REG_AARCH64_Q23: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q23); break;
            case triton::arch::ID_REG_AARCH64_Q24: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q24); break;
            case triton::arch::ID_REG_AARCH64_Q25: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q25); break;
            case triton::arch::ID_REG_AARCH64_Q26: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q26); break;
            case triton::arch::ID_REG_AARCH64_Q27: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q27); break;
            case triton::arch::ID_REG_AARCH64_Q28: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q28); break;
            case triton::arch::ID_REG_AARCH64_Q29: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q29); break;
            case triton::arch::ID_REG_AARCH64_Q30: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q30); break;
            case triton::arch::ID_REG_AARCH64_Q31: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q31); break;

            case triton::arch::ID_REG_AARCH64_V0:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q0);  break;
            case triton::arch::ID_REG_AARCH64_V1:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q1);  break;
            case triton::arch::ID_REG_AARCH64_V2:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q2);  break;
            case triton::arch::ID_REG_AARCH64_V3:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q3);  break;
            case triton::arch::ID_REG_AARCH64_V4:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q4);  break;
            case triton::arch::ID_REG_AARCH64_V5:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q5);  break;
            case triton::arch::ID_REG_AARCH64_V6:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q6);  break;
            case triton::arch::ID_REG_AARCH64_V7:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q7);  break;
            case triton::arch::ID_REG_AARCH64_V8:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q8);  break;
            case triton::arch::ID_REG_AARCH64_V9:  triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q9);  break;
            case triton::arch::ID_REG_AARCH64_V10: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q10); break;
            case triton::arch::ID_REG_AARCH64_V11: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q11); break;
            case triton::arch::ID_REG_AARCH64_V12: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q12); break;
            case triton::arch::ID_REG_AARCH64_V13: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q13); break;
            case triton::arch::ID_REG_AARCH64_V14: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q14); break;
            case triton::arch::ID_REG_AARCH64_V15: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q15); break;
            case triton::arch::ID_REG_AARCH64_V16: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q16); break;
            case triton::arch::ID_REG_AARCH64_V17: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q17); break;
            case triton::arch::ID_REG_AARCH64_V18: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q18); break;
            case triton::arch::ID_REG_AARCH64_V19: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q19); break;
            case triton::arch::ID_REG_AARCH64_V20: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q20); break;
            case triton::arch::ID_REG_AARCH64_V21: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q21); break;
            case triton::arch::ID_REG_AARCH64_V22: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q22); break;
            case triton::arch::ID_REG_AARCH64_V23: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q23); break;
            case triton::arch::ID_REG_AARCH64_V24: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q24); break;
            case triton::arch::ID_REG_AARCH64_V25: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q25); break;
            case triton::arch::ID_REG_AARCH64_V26: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q26); break;
            case triton::arch::ID_REG_AARCH64_V27: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q27); break;
            case triton::arch::ID_REG_AARCH64_V28: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q28); break;
            case triton::arch::ID_REG_AARCH64_V29: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q29); break;
            case triton::arch::ID_REG_AARCH64_V30: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q30); break;
            case triton::arch::ID_REG_AARCH64_V31: triton::utils::fromUintToBuffer(static_cast<triton::uint128>(value), this->q31); break;

            case triton::arch::ID_REG_AARCH64_D0:  (*((triton::uint64*)(this->q0)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D1:  (*((triton::uint64*)(this->q1)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D2:  (*((triton::uint64*)(this->q2)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D3:  (*((triton::uint64*)(this->q3)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D4:  (*((triton::uint64*)(this->q4)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D5:  (*((triton::uint64*)(this->q5)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D6:  (*((triton::uint64*)(this->q6)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D7:  (*((triton::uint64*)(this->q7)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D8:  (*((triton::uint64*)(this->q8)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D9:  (*((triton::uint64*)(this->q9)))  = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D10: (*((triton::uint64*)(this->q10))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D11: (*((triton::uint64*)(this->q11))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D12: (*((triton::uint64*)(this->q12))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D13: (*((triton::uint64*)(this->q13))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D14: (*((triton::uint64*)(this->q14))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D15: (*((triton::uint64*)(this->q15))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D16: (*((triton::uint64*)(this->q16))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D17: (*((triton::uint64*)(this->q17))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D18: (*((triton::uint64*)(this->q18))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D19: (*((triton::uint64*)(this->q19))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D20: (*((triton::uint64*)(this->q20))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D21: (*((triton::uint64*)(this->q21))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D22: (*((triton::uint64*)(this->q22))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D23: (*((triton::uint64*)(this->q23))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D24: (*((triton::uint64*)(this->q24))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D25: (*((triton::uint64*)(this->q25))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D26: (*((triton::uint64*)(this->q26))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D27: (*((triton::uint64*)(this->q27))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D28: (*((triton::uint64*)(this->q28))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D29: (*((triton::uint64*)(this->q29))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D30: (*((triton::uint64*)(this->q30))) = static_cast<triton::uint64>(value); break;
            case triton::arch::ID_REG_AARCH64_D31: (*((triton::uint64*)(this->q31))) = static_cast<triton::uint64>(value); break;

            case triton::arch::ID_REG_AARCH64_S0:  (*((triton::uint32*)(this->q0)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S1:  (*((triton::uint32*)(this->q1)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S2:  (*((triton::uint32*)(this->q2)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S3:  (*((triton::uint32*)(this->q3)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S4:  (*((triton::uint32*)(this->q4)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S5:  (*((triton::uint32*)(this->q5)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S6:  (*((triton::uint32*)(this->q6)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S7:  (*((triton::uint32*)(this->q7)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S8:  (*((triton::uint32*)(this->q8)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S9:  (*((triton::uint32*)(this->q9)))  = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S10: (*((triton::uint32*)(this->q10))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S11: (*((triton::uint32*)(this->q11))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S12: (*((triton::uint32*)(this->q12))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S13: (*((triton::uint32*)(this->q13))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S14: (*((triton::uint32*)(this->q14))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S15: (*((triton::uint32*)(this->q15))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S16: (*((triton::uint32*)(this->q16))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S17: (*((triton::uint32*)(this->q17))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S18: (*((triton::uint32*)(this->q18))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S19: (*((triton::uint32*)(this->q19))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S20: (*((triton::uint32*)(this->q20))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S21: (*((triton::uint32*)(this->q21))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S22: (*((triton::uint32*)(this->q22))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S23: (*((triton::uint32*)(this->q23))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S24: (*((triton::uint32*)(this->q24))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S25: (*((triton::uint32*)(this->q25))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S26: (*((triton::uint32*)(this->q26))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S27: (*((triton::uint32*)(this->q27))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S28: (*((triton::uint32*)(this->q28))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S29: (*((triton::uint32*)(this->q29))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S30: (*((triton::uint32*)(this->q30))) = static_cast<triton::uint32>(value); break;
            case triton::arch::ID_REG_AARCH64_S31: (*((triton::uint32*)(this->q31))) = static_cast<triton::uint32>(value); break;

            case triton::arch::ID_REG_AARCH64_H0:  (*((triton::uint16*)(this->q0)))  = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H1:  (*((triton::uint16*)(this->q1)))  = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H2:  (*((triton::uint16*)(this->q2)))  = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H3:  (*((triton::uint16*)(this->q3)))  = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H4:  (*((triton::uint16*)(this->q4)))  = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H5:  (*((triton::uint16*)(this->q5)))  = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H6:  (*((triton::uint16*)(this->q6)))  = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H7:  (*((triton::uint16*)(this->q7)))  = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H8:  (*((triton::uint16*)(this->q8)))  = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H9:  (*((triton::uint16*)(this->q9)))  = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H10: (*((triton::uint16*)(this->q10))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H11: (*((triton::uint16*)(this->q11))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H12: (*((triton::uint16*)(this->q12))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H13: (*((triton::uint16*)(this->q13))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H14: (*((triton::uint16*)(this->q14))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H15: (*((triton::uint16*)(this->q15))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H16: (*((triton::uint16*)(this->q16))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H17: (*((triton::uint16*)(this->q17))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H18: (*((triton::uint16*)(this->q18))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H19: (*((triton::uint16*)(this->q19))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H20: (*((triton::uint16*)(this->q20))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H21: (*((triton::uint16*)(this->q21))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H22: (*((triton::uint16*)(this->q22))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H23: (*((triton::uint16*)(this->q23))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H24: (*((triton::uint16*)(this->q24))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H25: (*((triton::uint16*)(this->q25))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H26: (*((triton::uint16*)(this->q26))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H27: (*((triton::uint16*)(this->q27))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H28: (*((triton::uint16*)(this->q28))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H29: (*((triton::uint16*)(this->q29))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H30: (*((triton::uint16*)(this->q30))) = static_cast<triton::uint16>(value); break;
            case triton::arch::ID_REG_AARCH64_H31: (*((triton::uint16*)(this->q31))) = static_cast<triton::uint16>(value); break;

            case triton::arch::ID_REG_AARCH64_B0:  (*((triton::uint8*)(this->q0)))  = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B1:  (*((triton::uint8*)(this->q1)))  = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B2:  (*((triton::uint8*)(this->q2)))  = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B3:  (*((triton::uint8*)(this->q3)))  = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B4:  (*((triton::uint8*)(this->q4)))  = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B5:  (*((triton::uint8*)(this->q5)))  = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B6:  (*((triton::uint8*)(this->q6)))  = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B7:  (*((triton::uint8*)(this->q7)))  = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B8:  (*((triton::uint8*)(this->q8)))  = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B9:  (*((triton::uint8*)(this->q9)))  = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B10: (*((triton::uint8*)(this->q10))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B11: (*((triton::uint8*)(this->q11))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B12: (*((triton::uint8*)(this->q12))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B13: (*((triton::uint8*)(this->q13))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B14: (*((triton::uint8*)(this->q14))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B15: (*((triton::uint8*)(this->q15))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B16: (*((triton::uint8*)(this->q16))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B17: (*((triton::uint8*)(this->q17))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B18: (*((triton::uint8*)(this->q18))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B19: (*((triton::uint8*)(this->q19))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B20: (*((triton::uint8*)(this->q20))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B21: (*((triton::uint8*)(this->q21))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B22: (*((triton::uint8*)(this->q22))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B23: (*((triton::uint8*)(this->q23))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B24: (*((triton::uint8*)(this->q24))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B25: (*((triton::uint8*)(this->q25))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B26: (*((triton::uint8*)(this->q26))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B27: (*((triton::uint8*)(this->q27))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B28: (*((triton::uint8*)(this->q28))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B29: (*((triton::uint8*)(this->q29))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B30: (*((triton::uint8*)(this->q30))) = static_cast<triton::uint8>(value); break;
            case triton::arch::ID_REG_AARCH64_B31: (*((triton::uint8*)(this->q31))) = static_cast<triton::uint8>(value); break;

            //! System registers
            #define SYS_REG_SPEC(UPPER_NAME, LOWER_NAME, _2, _3, _4, _5) \
            case triton::arch::ID_REG_AARCH64_##UPPER_NAME: (*((triton::uint64*)(this->LOWER_NAME))) = static_cast<triton::uint64>(value); break;
            #define REG_SPEC(_1, _2, _3, _4, _5, _6)
            #define REG_SPEC_NO_CAPSTONE(_1, _2, _3, _4, _5, _6)
            #include "triton/aarch64.spec"

            default:
              throw triton::exceptions::Cpu("AArch64Cpu:setConcreteRegisterValue(): Invalid register.");
          }
        }


        bool AArch64Cpu::isThumb(void) const {
          /* There is no thumb mode in aarch64 */
          return false;
        }


        void AArch64Cpu::setThumb(bool state) {
          /* There is no thumb mode in aarch64 */
        }


        bool AArch64Cpu::isMemoryExclusive(const triton::arch::MemoryAccess& mem) const {
          triton::uint64 base = mem.getAddress();

          for (triton::usize index = 0; index < mem.getSize(); index++) {
            if (this->exclusiveMemoryTags.find(base + index) != this->exclusiveMemoryTags.end()) {
              return true;
            }
          }

          return false;
        }


        void AArch64Cpu::setMemoryExclusiveTag(const triton::arch::MemoryAccess& mem, bool tag) {
          triton::uint64 base = mem.getAddress();

          for (triton::usize index = 0; index < mem.getSize(); index++) {
            if (tag == true) {
              this->exclusiveMemoryTags.insert(base + index);
            }
            else {
              this->exclusiveMemoryTags.erase(base + index);
            }
          }
        }


        bool AArch64Cpu::isConcreteMemoryValueDefined(const triton::arch::MemoryAccess& mem) const {
          return this->isConcreteMemoryValueDefined(mem.getAddress(), mem.getSize());
        }


        bool AArch64Cpu::isConcreteMemoryValueDefined(triton::uint64 baseAddr, triton::usize size) const {
          for (triton::usize index = 0; index < size; index++) {
            if (this->memory.find(baseAddr + index) == this->memory.end())
              return false;
          }
          return true;
        }


        void AArch64Cpu::clearConcreteMemoryValue(const triton::arch::MemoryAccess& mem) {
          this->clearConcreteMemoryValue(mem.getAddress(), mem.getSize());
        }


        void AArch64Cpu::clearConcreteMemoryValue(triton::uint64 baseAddr, triton::usize size) {
          for (triton::usize index = 0; index < size; index++) {
            if (this->memory.find(baseAddr + index) != this->memory.end()) {
              this->memory.erase(baseAddr + index);
            }
          }
        }

      }; /* aarch64 namespace */
    }; /* arm namespace */
  }; /* arch namespace */
}; /* triton namespace */
