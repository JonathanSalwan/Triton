//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <operandWrapper.hpp>



namespace triton {
  namespace arch {

    OperandWrapper::OperandWrapper(ImmediateOperand imm) {
      this->imm = imm;
      this->type = triton::arch::OP_IMM;
    }


    OperandWrapper::OperandWrapper(MemoryOperand mem) {
      this->mem = mem;
      this->type = triton::arch::OP_MEM;
    }


    OperandWrapper::OperandWrapper(RegisterOperand reg) {
      this->reg = reg;
      this->type = triton::arch::OP_REG;
    };


    OperandWrapper::~OperandWrapper() {
    }


    triton::uint32 OperandWrapper::getType(void) const {
      return this->type;
    }


    ImmediateOperand& OperandWrapper::getImmediate(void) {
      return this->imm;
    }


    MemoryOperand& OperandWrapper::getMemory(void) {
      return this->mem;
    }


    RegisterOperand& OperandWrapper::getRegister(void) {
      return this->reg;
    }


    void OperandWrapper::setImmediate(ImmediateOperand imm) {
      this->imm = imm;
    }


    void OperandWrapper::setMemory(MemoryOperand mem) {
      this->mem = mem;
    }


    void OperandWrapper::setRegister(RegisterOperand reg) {
      this->reg = reg;
    }


    triton::uint32 OperandWrapper::getSize(void) {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return this->getImmediate().getSize();
        case triton::arch::OP_MEM: return this->getMemory().getSize();
        case triton::arch::OP_REG: return this->getRegister().getSize();
        default:
          throw std::invalid_argument("OperandWrapper::getSize(): Invalid type operand");
      }
      return 0;
    }


    triton::uint32 OperandWrapper::getBitSize(void) {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return this->getImmediate().getBitSize();
        case triton::arch::OP_MEM: return this->getMemory().getBitSize();
        case triton::arch::OP_REG: return this->getRegister().getBitSize();
        default:
          throw std::invalid_argument("OperandWrapper::getBitSize(): Invalid type operand");
      }
      return 0;
    }


    triton::uint32 OperandWrapper::getAbstractHigh(void) {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return this->getImmediate().getAbstractHigh();
        case triton::arch::OP_MEM: return this->getMemory().getAbstractHigh();
        case triton::arch::OP_REG: return this->getRegister().getAbstractHigh();
        default:
          throw std::invalid_argument("OperandWrapper::getHigh(): Invalid type operand");
      }
      return 0;
    }


    triton::uint32 OperandWrapper::getAbstractLow(void) {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return this->getImmediate().getAbstractLow();
        case triton::arch::OP_MEM: return this->getMemory().getAbstractLow();
        case triton::arch::OP_REG: return this->getRegister().getAbstractLow();
        default:
          throw std::invalid_argument("OperandWrapper::getLow(): Invalid type operand");
      }
      return 0;
    }


    triton::uint128 OperandWrapper::getConcreteValue(void) {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return this->getImmediate().getValue();
        case triton::arch::OP_MEM: return this->getMemory().getConcreteValue();
        case triton::arch::OP_REG: return this->getRegister().getConcreteValue();
        default:
          throw std::invalid_argument("OperandWrapper::getConcreteValue(): Invalid type operand");
      }
      return 0;
    }


    bool OperandWrapper::isTrusted(void) {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return true;
        case triton::arch::OP_MEM: return this->getMemory().isTrusted();
        case triton::arch::OP_REG: return this->getRegister().isTrusted();
        default:
          throw std::invalid_argument("OperandWrapper::isTrusted(): Invalid type operand");
      }
      return false;
    }


    void OperandWrapper::setTrust(bool flag) {
      switch (this->getType()) {
        case triton::arch::OP_IMM: break;
        case triton::arch::OP_MEM: this->getMemory().setTrust(flag); break;
        case triton::arch::OP_REG: this->getRegister().setTrust(flag); break;
        default:
          throw std::invalid_argument("OperandWrapper::setTrust(): Invalid type operand");
      }
    }


    std::ostream &operator<<(std::ostream &stream, triton::arch::OperandWrapper op) {
      switch (op.getType()) {
        case triton::arch::OP_IMM: stream << op.getImmediate(); break;
        case triton::arch::OP_MEM: stream << op.getMemory(); break;
        case triton::arch::OP_REG: stream << op.getRegister(); break;
        default:
          throw std::invalid_argument("triton::arch::operator<<(OperandWrapper): Invalid type operand");
      }
      return stream;
    }

  };
};
