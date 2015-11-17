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


BitsVector::BitsVector(reg_size high, reg_size low) {
  this->high = high;
  this->low  = low;
}


BitsVector::BitsVector(const BitsVector &copy) {
  this->high = copy.high;
  this->low  = copy.low;
}


BitsVector::~BitsVector() {
}


std::pair<reg_size, reg_size> BitsVector::getPair(void) {
  return std::make_pair(this->high, this->low);
}


reg_size BitsVector::getHigh(void) {
  return this->high;
}


reg_size BitsVector::getLow(void) {
  return this->low;
}


reg_size BitsVector::getVectorSize(void) {
  return (this->high - this->low) + 1;
}


void BitsVector::setHigh(reg_size v) {
  this->high = v;
}


void BitsVector::setLow(reg_size v) {
  this->low = v;
}


void BitsVector::setPair(std::pair<reg_size, reg_size> p) {
  this->high = std::get<0>(p);
  this->low  = std::get<1>(p);
}

