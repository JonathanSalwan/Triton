/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <Smodel.h>


Smodel::Smodel(std::string name, __uint value) {
  this->name = name;
  this->value = value;
}


Smodel::~Smodel() {
}


std::string Smodel::getName(void) {
  return this->name;
}


__uint Smodel::getValue(void) {
  return this->value;
}

#endif /* LIGHT_VERSION */

