/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <RegisterOperand.h>
#include <PINConverter.h>


RegisterOperand::RegisterOperand(uint64 regId) {
  this->id = regId
}


RegisterOperand::~RegisterOperand() {
}


uint64 RegisterOperand::getId(void) {
  return this->id;
}


const std::string& RegisterOperand::getName(void) {
  return this->name;
}


const ExtractBits& RegisterOperand::getBitsVector(void) {
  return this->bitsVector;
}

