/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <MemoryOperand.h>


MemoryOperand::MemoryOperand(void) {
  this->address = 0;
  this->size    = 0;
}


MemoryOperand::MemoryOperand(uint64 address, uint64 size) {
  this->address = address;
  this->size    = size;
}


MemoryOperand::MemoryOperand(const MemoryOperand& other) {
  this->copy(other);
}


MemoryOperand::~MemoryOperand() {
}


uint64 MemoryOperand::getAddress(void) const {
  return this->address;
}


uint64 MemoryOperand::getSize(void) const {
  return this->size;
}


void MemoryOperand::setAddress(uint64 addr) {
  this->address = addr;
}


void MemoryOperand::setSize(uint64 size) {
  this->size = size;
}


void MemoryOperand::operator=(const MemoryOperand &other) {
  this->copy(other);
}


void MemoryOperand::copy(const MemoryOperand& other) {
  this->address = other.address;
  this->size    = other.size;
}

