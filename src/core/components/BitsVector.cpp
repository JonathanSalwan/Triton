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


BitsVector::BitsVector(__uint high, __uint low) {
  this->high = high;
  this->low  = low;
}


BitsVector::BitsVector(const BitsVector &copy) {
  this->high = copy.high;
  this->low  = copy.low;
}


BitsVector::~BitsVector() {
}


std::pair<__uint, __uint> BitsVector::getPair(void) const {
  return std::make_pair(this->high, this->low);
}


__uint BitsVector::getHigh(void) const {
  return this->high;
}


__uint BitsVector::getLow(void) const {
  return this->low;
}


__uint BitsVector::getVectorSize(void) const {
  return (this->high - this->low) + 1;
}


void BitsVector::setHigh(__uint v) {
  this->high = v;
}


void BitsVector::setLow(__uint v) {
  this->low = v;
}


void BitsVector::setPair(std::pair<__uint, __uint> p) {
  this->high = std::get<0>(p);
  this->low  = std::get<1>(p);
}


void BitsVector::operator=(const BitsVector& other) {
  this->high = other.high;
  this->low  = other.low;
}

