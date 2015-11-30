/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <PINConverter.h>
#include <RegisterOperand.h>
#include <pin.H>



RegisterOperand::RegisterOperand()
  : name("") {
  this->tritonRegId = 0;
  this->pinRegId    = 0;
  this->size        = 0;
}


RegisterOperand::RegisterOperand(__uint pinRegId, __uint size)
  : name("") {
  this->tritonRegId = PINConverter::convertDBIReg2TritonReg(pinRegId);
  this->pinRegId    = PINConverter::convertTritonReg2DBIReg(this->tritonRegId);
  this->size        = size;

  if (REG_valid(static_cast<REG>(pinRegId))) {
    // check needed because instructions like "xgetbv 0" make
    // REG_Size crash.
    if (!this->size)
      this->size = REG_Size(static_cast<REG>(pinRegId));
    this->name = REG_StringShort(static_cast<REG>(pinRegId));
  }

  this->setPair(PINConverter::convertDBIReg2BitsVector(pinRegId));
}


RegisterOperand::RegisterOperand(const RegisterOperand& other) {
  this->copy(other);
}


RegisterOperand::~RegisterOperand() {
}


__uint RegisterOperand::getAbstractLow(void) const {
  return this->getLow();
}


__uint RegisterOperand::getAbstractHigh(void) const {
  return this->getHigh();
}


__uint RegisterOperand::getTritonRegId(void) const {
  return this->tritonRegId;
}


__uint RegisterOperand::getPinRegId(void) const {
  return this->pinRegId;
}


__uint RegisterOperand::getBitSize(void) const {
  return (this->size * BYTE_SIZE_BIT);
}


__uint RegisterOperand::getSize(void) const {
  return this->size;
}


std::string RegisterOperand::getName(void) const {
  return this->name;
}


void RegisterOperand::setSize(__uint size) {
  this->size = size;
}


void RegisterOperand::setTritonRegId(__uint tritonRegId) {
  this->tritonRegId = tritonRegId;
}


bool RegisterOperand::isValid(void) {
  if (this->tritonRegId == ID_INVALID)
    return false;
  return true;
}


void RegisterOperand::operator=(const RegisterOperand& other) {
  this->copy(other);
}


void RegisterOperand::copy(const RegisterOperand& other) {
  this->high        = other.high;
  this->low         = other.low;
  this->pinRegId    = other.pinRegId;
  this->size        = other.size;
  this->tritonRegId = other.tritonRegId;
  this->name        = other.name;
}

