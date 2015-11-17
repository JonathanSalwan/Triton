/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <ImmediateOperand.h>


ImmediateOperand::ImmediateOperand() {
  this->value = 0;
}


ImmediateOperand::ImmediateOperand(reg_size value) {
  this->value = value;
}


ImmediateOperand::ImmediateOperand(const ImmediateOperand& other) {
  this->copy(other);
}


ImmediateOperand::~ImmediateOperand() {
}


reg_size ImmediateOperand::getValue(void) const {
  return this->value;
}


void ImmediateOperand::setValue(reg_size v) {
  this->value = v;
}


void ImmediateOperand::operator=(const ImmediateOperand& other) {
  this->copy(other);
}


void ImmediateOperand::copy(const ImmediateOperand& other) {
  this->value = other.value;
}

