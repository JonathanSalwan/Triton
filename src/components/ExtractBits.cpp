/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <ExtractBits.h>



ExtractBits::ExtractBits() {
  this->high = 0;
  this->low  = 0;
}


ExtractBits::ExtractBits(uint64 high, uint64 low) {
  this->high = high;
  this->low  = low;
}


ExtractBits::ExtractBits(const ExtractBits &copy) {
  this->high = copy.high;
  this->low  = copy.low;
}


ExtractBits::~ExtractBits() {
}


std::pair<uint64, uint64> ExtractBits::getPair(void) {
  return std::make_pair(this->high, this->low);
}


uint64 ExtractBits::getHigh(void) {
  return this->high;
}


uint64 ExtractBits::getLow(void) {
  return this->low;
}


uint64 ExtractBits::getVectorSize(void) {
  return (this->high - this->low) + 1;
}


void ExtractBits::setHigh(uint64 v) {
  this->high = v;
}


void ExtractBits::setLow(uint64 v) {
  this->low = v;
}

