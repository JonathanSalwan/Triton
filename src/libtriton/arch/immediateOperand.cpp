//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <cpuSize.hpp>
#include <immediateOperand.hpp>



namespace triton {
  namespace arch {

    ImmediateOperand::ImmediateOperand() {
      this->value = 0;
    }


    ImmediateOperand::ImmediateOperand(triton::__uint value, triton::uint32 size) {
      this->value = value;
      if (size == 0)
        throw std::runtime_error("ImmediateOperand::ImmediateOperand(): size cannot be zero.");
      if (size > DQWORD_SIZE)
        throw std::runtime_error("ImmediateOperand::ImmediateOperand(): size cannot be greater than a DQWORD.");
      this->setPair(std::make_pair(((size * BYTE_SIZE_BIT) - 1), 0));
    }


    ImmediateOperand::ImmediateOperand(const ImmediateOperand& other) {
      this->copy(other);
    }


    ImmediateOperand::~ImmediateOperand() {
    }


    triton::__uint ImmediateOperand::getValue(void) const {
      return this->value;
    }


    void ImmediateOperand::setValue(triton::__uint v) {
      this->value = v;
    }


    triton::uint32 ImmediateOperand::getAbstractLow(void) const {
      return this->getLow();
    }


    triton::uint32 ImmediateOperand::getAbstractHigh(void) const {
      return this->getHigh();
    }


    triton::uint32 ImmediateOperand::getSize(void) const {
      return this->getVectorSize() / BYTE_SIZE_BIT;
    }


    triton::uint32 ImmediateOperand::getBitSize(void) const {
      return this->getVectorSize();
    }


    triton::uint32 ImmediateOperand::getType(void) const {
      return triton::arch::OP_IMM;
    }


    void ImmediateOperand::operator=(const ImmediateOperand& other) {
      this->copy(other);
    }


    void ImmediateOperand::copy(const ImmediateOperand& other) {
      this->high  = other.high;
      this->low   = other.low;
      this->value = other.value;
    }


    std::ostream &operator<<(std::ostream &stream, ImmediateOperand imm) {
      stream << "0x" << std::hex << imm.getValue() << ":" << std::dec << imm.getBitSize() << " bv[" << imm.getHigh() << ".." << imm.getLow() << "]";
      return stream;
    }

  }; /* arch namespace */
}; /* triton namespace */
