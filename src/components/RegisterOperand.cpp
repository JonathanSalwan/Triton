/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <PINConverter.h>
#include <RegisterOperand.h>
#include <pin.H>


RegisterOperand::RegisterOperand() {
  this->tritonRegId = 0;
  this->pinRegId    = 0;
  this->size        = 0;
}


RegisterOperand::RegisterOperand(uint64 pinRegId) {
  this->tritonRegId = PINConverter::convertDBIReg2TritonReg(pinRegId);
  this->pinRegId    = PINConverter::convertTritonReg2DBIReg(this->tritonRegId);

  if (REG_valid(static_cast<REG>(pinRegId))) {
    // check needed because instructions like "xgetbv 0" make
    // REG_Size crash.
    this->size = REG_Size(static_cast<REG>(pinRegId));
  }

  this->setPair(PINConverter::convertDBIReg2BitsVector(pinRegId));
}


RegisterOperand::~RegisterOperand() {
}


uint64 RegisterOperand::getTritonRegId(void) const {
  return this->tritonRegId;
}


uint64 RegisterOperand::getPinRegId(void) const {
  return this->pinRegId;
}


uint64 RegisterOperand::getSize(void) const {
  return this->size;
}


void RegisterOperand::setSize(uint64 size) {
  this->size = size;
}


void RegisterOperand::operator=(const RegisterOperand &other) {
  this->high        = other.high;
  this->low         = other.low;
  this->pinRegId    = other.pinRegId;
  this->size        = other.size;
  this->tritonRegId = other.tritonRegId;
}

