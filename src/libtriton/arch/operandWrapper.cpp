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


    ImmediateOperand& OperandWrapper::getImm(void) {
      return this->imm;
    }


    MemoryOperand& OperandWrapper::getMem(void) {
      return this->mem;
    }


    RegisterOperand& OperandWrapper::getReg(void) {
      return this->reg;
    }


    void OperandWrapper::setImm(ImmediateOperand imm) {
      this->imm = imm;
    }


    void OperandWrapper::setMem(MemoryOperand mem) {
      this->mem = mem;
    }


    void OperandWrapper::setReg(RegisterOperand reg) {
      this->reg = reg;
    }


    triton::uint32 OperandWrapper::getSize(void) {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return this->getImm().getSize();
        case triton::arch::OP_MEM: return this->getMem().getSize();
        case triton::arch::OP_REG: return this->getReg().getSize();
        default:
          throw std::invalid_argument("OperandWrapper::getSize(): Invalid type operand");
      }
      return 0;
    }


    triton::uint32 OperandWrapper::getBitSize(void) {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return this->getImm().getBitSize();
        case triton::arch::OP_MEM: return this->getMem().getBitSize();
        case triton::arch::OP_REG: return this->getReg().getBitSize();
        default:
          throw std::invalid_argument("OperandWrapper::getBitSize(): Invalid type operand");
      }
      return 0;
    }


    triton::uint32 OperandWrapper::getAbstractHigh(void) {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return this->getImm().getAbstractHigh();
        case triton::arch::OP_MEM: return this->getMem().getAbstractHigh();
        case triton::arch::OP_REG: return this->getReg().getAbstractHigh();
        default:
          throw std::invalid_argument("OperandWrapper::getHigh(): Invalid type operand");
      }
      return 0;
    }


    triton::uint32 OperandWrapper::getAbstractLow(void) {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return this->getImm().getAbstractLow();
        case triton::arch::OP_MEM: return this->getMem().getAbstractLow();
        case triton::arch::OP_REG: return this->getReg().getAbstractLow();
        default:
          throw std::invalid_argument("OperandWrapper::getLow(): Invalid type operand");
      }
      return 0;
    }


    triton::uint128 OperandWrapper::getConcreteValue(void) {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return this->getImm().getValue();
        case triton::arch::OP_MEM: return this->getMem().getConcreteValue();
        case triton::arch::OP_REG: return this->getReg().getConcreteValue();
        default:
          throw std::invalid_argument("OperandWrapper::getConcreteValue(): Invalid type operand");
      }
      return 0;
    }


    bool OperandWrapper::isTrusted(void) {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return true;
        case triton::arch::OP_MEM: return this->getMem().isTrusted();
        case triton::arch::OP_REG: return this->getReg().isTrusted();
        default:
          throw std::invalid_argument("OperandWrapper::isTrusted(): Invalid type operand");
      }
      return false;
    }


    void OperandWrapper::setTrust(bool flag) {
      switch (this->getType()) {
        case triton::arch::OP_IMM: break;
        case triton::arch::OP_MEM: this->getMem().setTrust(flag); break;
        case triton::arch::OP_REG: this->getReg().setTrust(flag); break;
        default:
          throw std::invalid_argument("OperandWrapper::setTrust(): Invalid type operand");
      }
    }


    std::ostream &operator<<(std::ostream &stream, triton::arch::OperandWrapper op) {
      switch (op.getType()) {
        case triton::arch::OP_IMM: stream << op.getImm(); break;
        case triton::arch::OP_MEM: stream << op.getMem(); break;
        case triton::arch::OP_REG: stream << op.getReg(); break;
        default:
          throw std::invalid_argument("triton::arch::operator<<(OperandWrapper): Invalid type operand");
      }
      return stream;
    }

  };
};
