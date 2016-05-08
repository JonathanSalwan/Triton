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

    OperandWrapper::OperandWrapper(const ImmediateOperand& imm) {
      this->imm = imm;
      this->type = triton::arch::OP_IMM;
    }


    OperandWrapper::OperandWrapper(const MemoryOperand& mem) {
      this->mem = mem;
      this->type = triton::arch::OP_MEM;
    }


    OperandWrapper::OperandWrapper(const RegisterOperand& reg) {
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


    const ImmediateOperand& OperandWrapper::getConstImmediate(void) const {
      return this->imm;
    }


    const MemoryOperand& OperandWrapper::getConstMemory(void) const {
      return this->mem;
    }


    const RegisterOperand& OperandWrapper::getConstRegister(void) const {
      return this->reg;
    }


    void OperandWrapper::setImmediate(const ImmediateOperand& imm) {
      this->imm = imm;
    }


    void OperandWrapper::setMemory(const MemoryOperand& mem) {
      this->mem = mem;
    }


    void OperandWrapper::setRegister(const RegisterOperand& reg) {
      this->reg = reg;
    }


    triton::uint32 OperandWrapper::getSize(void) const {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return this->getConstImmediate().getSize();
        case triton::arch::OP_MEM: return this->getConstMemory().getSize();
        case triton::arch::OP_REG: return this->getConstRegister().getSize();
        default:
          throw std::invalid_argument("OperandWrapper::getSize(): Invalid type operand.");
      }
      return 0;
    }


    triton::uint32 OperandWrapper::getBitSize(void) const {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return this->getConstImmediate().getBitSize();
        case triton::arch::OP_MEM: return this->getConstMemory().getBitSize();
        case triton::arch::OP_REG: return this->getConstRegister().getBitSize();
        default:
          throw std::invalid_argument("OperandWrapper::getBitSize(): Invalid type operand.");
      }
      return 0;
    }


    triton::uint32 OperandWrapper::getAbstractHigh(void) const {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return this->getConstImmediate().getAbstractHigh();
        case triton::arch::OP_MEM: return this->getConstMemory().getAbstractHigh();
        case triton::arch::OP_REG: return this->getConstRegister().getAbstractHigh();
        default:
          throw std::invalid_argument("OperandWrapper::getHigh(): Invalid type operand.");
      }
      return 0;
    }


    triton::uint32 OperandWrapper::getAbstractLow(void) const {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return this->getConstImmediate().getAbstractLow();
        case triton::arch::OP_MEM: return this->getConstMemory().getAbstractLow();
        case triton::arch::OP_REG: return this->getConstRegister().getAbstractLow();
        default:
          throw std::invalid_argument("OperandWrapper::getLow(): Invalid type operand.");
      }
      return 0;
    }


    triton::uint512 OperandWrapper::getConcreteValue(void) const {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return this->getConstImmediate().getValue();
        case triton::arch::OP_MEM: return this->getConstMemory().getConcreteValue();
        case triton::arch::OP_REG: return this->getConstRegister().getConcreteValue();
        default:
          throw std::invalid_argument("OperandWrapper::getConcreteValue(): Invalid type operand.");
      }
      return 0;
    }


    bool OperandWrapper::isTrusted(void) const {
      switch (this->getType()) {
        case triton::arch::OP_IMM: return true;
        case triton::arch::OP_MEM: return this->getConstMemory().isTrusted();
        case triton::arch::OP_REG: return this->getConstRegister().isTrusted();
        default:
          throw std::invalid_argument("OperandWrapper::isTrusted(): Invalid type operand.");
      }
      return false;
    }


    void OperandWrapper::setTrust(bool flag) {
      switch (this->getType()) {
        case triton::arch::OP_IMM: break;
        case triton::arch::OP_MEM: this->getMemory().setTrust(flag); break;
        case triton::arch::OP_REG: this->getRegister().setTrust(flag); break;
        default:
          throw std::invalid_argument("OperandWrapper::setTrust(): Invalid type operand.");
      }
    }


    void OperandWrapper::operator=(const OperandWrapper& other) {
      this->imm  = other.imm;
      this->mem  = other.mem;
      this->reg  = other.reg;
      this->type = other.type;
    }


    std::ostream& operator<<(std::ostream& stream, const triton::arch::OperandWrapper& op) {
      switch (op.getType()) {
        case triton::arch::OP_IMM: stream << op.getConstImmediate(); break;
        case triton::arch::OP_MEM: stream << op.getConstMemory(); break;
        case triton::arch::OP_REG: stream << op.getConstRegister(); break;
        default:
          throw std::invalid_argument("triton::arch::operator<<(OperandWrapper): Invalid type operand.");
      }
      return stream;
    }


    std::ostream& operator<<(std::ostream &stream, const triton::arch::OperandWrapper* op) {
      stream << *op;
      return stream;
    }

  };
};
