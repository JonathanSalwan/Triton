/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <ImmediateOperand.h>


ImmediateOperand::ImmediateOperand() {
  this->value = 0;
}


ImmediateOperand::ImmediateOperand(uint64 value) {
  this->value = value;
}


ImmediateOperand::ImmediateOperand(const ImmediateOperand& other) {
  this->copy(other);
}


ImmediateOperand::~ImmediateOperand() {
}


uint64 ImmediateOperand::getValue(void) const {
  return this->value;
}


void ImmediateOperand::setValue(uint64 v) {
  this->value = v;
}


void ImmediateOperand::operator=(const ImmediateOperand& other) {
  this->copy(other);
}


void ImmediateOperand::copy(const ImmediateOperand& other) {
  this->value = other.value;
}

