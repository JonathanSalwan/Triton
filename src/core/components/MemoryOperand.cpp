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


MemoryOperand::MemoryOperand(reg_size address, reg_size size) {
  this->address = address;
  this->size    = size;
  if (size == 0)
    throw std::runtime_error("MemoryOperand::MemoryOperand() - size cannot be zero");
  this->setPair(std::make_pair(((size * REG_SIZE) - 1 ), 0));
}


MemoryOperand::MemoryOperand(const MemoryOperand& other) {
  this->copy(other);
}


MemoryOperand::~MemoryOperand() {
}


reg_size MemoryOperand::getAddress(void) const {
  return this->address;
}


reg_size MemoryOperand::getSize(void) const {
  return this->size;
}


void MemoryOperand::setAddress(reg_size addr) {
  this->address = addr;
}


void MemoryOperand::setSize(reg_size size) {
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

