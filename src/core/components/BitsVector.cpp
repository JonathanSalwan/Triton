/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <BitsVector.h>



BitsVector::BitsVector() {
  this->high = 0;
  this->low  = 0;
}


BitsVector::BitsVector(uint64 high, uint64 low) {
  this->high = high;
  this->low  = low;
}


BitsVector::BitsVector(const BitsVector &copy) {
  this->high = copy.high;
  this->low  = copy.low;
}


BitsVector::~BitsVector() {
}


std::pair<uint64, uint64> BitsVector::getPair(void) {
  return std::make_pair(this->high, this->low);
}


uint64 BitsVector::getHigh(void) {
  return this->high;
}


uint64 BitsVector::getLow(void) {
  return this->low;
}


uint64 BitsVector::getVectorSize(void) {
  return (this->high - this->low) + 1;
}


void BitsVector::setHigh(uint64 v) {
  this->high = v;
}


void BitsVector::setLow(uint64 v) {
  this->low = v;
}


void BitsVector::setPair(std::pair<uint64, uint64> p) {
  this->high = std::get<0>(p);
  this->low  = std::get<1>(p);
}

