/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <CpuSize.h>
#include <MemoryOperand.h>


MemoryOperand::MemoryOperand(void) {
  this->address = 0;
  this->size    = 0;
}


MemoryOperand::MemoryOperand(__uint address, __uint size) {
  this->address = address;
  this->size    = size;
  if (size == 0)
    throw std::runtime_error("MemoryOperand::MemoryOperand() - size cannot be zero");
  this->setPair(std::make_pair(((size * BYTE_SIZE_BIT) - 1), 0));
}


MemoryOperand::MemoryOperand(const MemoryOperand& other) {
  this->copy(other);
}


MemoryOperand::~MemoryOperand() {
}


__uint MemoryOperand::getAbstractLow(void) const {
  return this->getLow();
}


__uint MemoryOperand::getAbstractHigh(void) const {
  return this->getHigh();
}


__uint MemoryOperand::getAddress(void) const {
  return this->address;
}


__uint MemoryOperand::getBitSize(void) const {
  return (this->size * BYTE_SIZE_BIT);
}


__uint MemoryOperand::getSize(void) const {
  return this->size;
}


void MemoryOperand::setAddress(__uint addr) {
  this->address = addr;
}


void MemoryOperand::setSize(__uint size) {
  this->size = size;
}


void MemoryOperand::operator=(const MemoryOperand &other) {
  this->copy(other);
}


void MemoryOperand::copy(const MemoryOperand& other) {
  this->address = other.address;
  this->high    = other.high;
  this->low     = other.low;
  this->size    = other.size;
}

