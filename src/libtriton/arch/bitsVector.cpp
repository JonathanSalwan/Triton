//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/bitsVector.hpp>
#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>



namespace triton {
  namespace arch {

    BitsVector::BitsVector() {
      this->high = 0;
      this->low  = 0;
    }


    BitsVector::BitsVector(triton::uint32 high /* bits */, triton::uint32 low /* bits */) {
      this->setBits(high, low);
    }


    BitsVector::BitsVector(const BitsVector &other) {
      this->high = other.high;
      this->low  = other.low;
    }


    triton::uint32 BitsVector::getHigh(void) const {
      return this->high;
    }


    triton::uint32 BitsVector::getLow(void) const {
      return this->low;
    }


    triton::uint32 BitsVector::getVectorSize(void) const {
      return (this->high - this->low) + 1;
    }


    triton::uint512 BitsVector::getMaxValue(void) const {
      triton::uint512 max = -1;
      max = max >> (512 - this->getVectorSize());
      return max;
    }


    void BitsVector::setHigh(triton::uint32 v) {
      this->high = v;

      if (this->high >= triton::bitsize::max_supported)
        throw triton::exceptions::BitsVector("BitsVector::setHigh(): The highest bit cannot be greater than triton::bitsize::max_supported.");
    }


    void BitsVector::setLow(triton::uint32 v) {
      this->low = v;

      if (this->low > this->high)
        throw triton::exceptions::BitsVector("BitsVector::setLow(): The lower bit cannot be greater than highest.");
    }


    void BitsVector::setBits(triton::uint32 high, triton::uint32 low) {
      this->high = high;
      this->low = low;

      if (this->high >= triton::bitsize::max_supported)
        throw triton::exceptions::BitsVector("BitsVector::setBits(): The highest bit cannot be greater than triton::bitsize::max_supported.");

      if (this->low > this->high)
        throw triton::exceptions::BitsVector("BitsVector::setBits(): The lower bit cannot be greater than highest.");
    }


    BitsVector& BitsVector::operator=(const BitsVector& other) {
      this->high = other.high;
      this->low  = other.low;
      return *this;
    }


    std::ostream& operator<<(std::ostream& stream, const BitsVector& bv) {
      stream << "bv[" << bv.getHigh() << ".." << bv.getLow() << "]";
      return stream;
    }


    std::ostream& operator<<(std::ostream& stream, const BitsVector* bv) {
      stream << *bv;
      return stream;
    }

  }; /* arch namespace */
}; /* triton namespace */
