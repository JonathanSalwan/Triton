//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <cpuSize.hpp>
#include <memoryOperand.hpp>



namespace triton {
  namespace arch {

    MemoryOperand::MemoryOperand(void) {
      this->address       = 0;
      this->concreteValue = 0;
      this->trusted       = false;
    }


    MemoryOperand::MemoryOperand(triton::__uint address, triton::uint32 size /* bytes */, triton::uint128 concreteValue) {
      this->address       = address;
      this->concreteValue = concreteValue;
      this->trusted       = true;

      if (size == 0)
        throw std::runtime_error("MemoryOperand::MemoryOperand(): size cannot be zero.");

      if (size > DQWORD_SIZE)
        throw std::runtime_error("MemoryOperand::MemoryOperand(): size cannot be greater than a DQWORD.");

      this->setPair(std::make_pair(((size * BYTE_SIZE_BIT) - 1), 0));
    }


    MemoryOperand::MemoryOperand(const MemoryOperand& other) {
      this->copy(other);
    }


    MemoryOperand::~MemoryOperand() {
    }


    triton::uint32 MemoryOperand::getAbstractLow(void) const {
      return this->getLow();
    }


    triton::uint32 MemoryOperand::getAbstractHigh(void) const {
      return this->getHigh();
    }


    triton::__uint MemoryOperand::getAddress(void) const {
      return this->address;
    }


    triton::uint32 MemoryOperand::getBitSize(void) const {
      return this->getVectorSize();
    }


    triton::uint128 MemoryOperand::getConcreteValue(void) const {
      return this->concreteValue;
    }


    triton::uint32 MemoryOperand::getSize(void) const {
      return this->getVectorSize() / BYTE_SIZE_BIT;
    }


    triton::uint32 MemoryOperand::getType(void) const {
      return triton::arch::OP_MEM;
    }


    RegisterOperand& MemoryOperand::getBaseReg(void) {
      return this->baseReg;
    }


    RegisterOperand& MemoryOperand::getIndexReg(void) {
      return this->indexReg;
    }


    ImmediateOperand& MemoryOperand::getDisplacement(void) {
      return this->displacement;
    }


    ImmediateOperand& MemoryOperand::getScale(void) {
      return this->scale;
    }


    bool MemoryOperand::isTrusted(void) {
      return this->trusted;
    }


    bool MemoryOperand::isValid(void) {
      if (!this->address && !this->concreteValue && !this->trusted && !this->getLow() && !this->getHigh())
        return false;
      return true;
    }


    void MemoryOperand::setTrust(bool flag) {
      this->trusted = flag;
    }


    void MemoryOperand::setAddress(triton::__uint addr) {
      this->address = addr;
    }


    void MemoryOperand::setConcreteValue(triton::uint128 concreteValue) {
      this->concreteValue = concreteValue;
      this->trusted       = true;
    }


    void MemoryOperand::setBaseReg(RegisterOperand base) {
      this->baseReg = base;
    }


    void MemoryOperand::setIndexReg(RegisterOperand index) {
      this->indexReg = index;
    }


    void MemoryOperand::setDisplacement(ImmediateOperand displacement) {
      this->displacement = displacement;
    }


    void MemoryOperand::setScale(ImmediateOperand scale) {
      this->scale = scale;
    }


    void MemoryOperand::operator=(const MemoryOperand &other) {
      this->copy(other);
    }


    void MemoryOperand::copy(const MemoryOperand& other) {
      this->address       = other.address;
      this->baseReg       = other.baseReg;
      this->concreteValue = other.concreteValue;
      this->displacement  = other.displacement;
      this->high          = other.high;
      this->indexReg      = other.indexReg;
      this->low           = other.low;
      this->scale         = other.scale;
      this->trusted       = other.trusted;
    }


    std::ostream &operator<<(std::ostream &stream, MemoryOperand mem) {
      stream << "*[0x" << std::hex << mem.getAddress() << "]:" << std::dec << mem.getBitSize() << " bv[" << mem.getHigh() << ".." << mem.getLow() << "]";
      return stream;
    }

  }; /* arch namespace */
}; /* triton namespace */
