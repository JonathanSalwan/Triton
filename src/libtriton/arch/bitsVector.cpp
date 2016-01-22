//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <bitsVector.hpp>
#include <cpuSize.hpp>



namespace triton {
  namespace arch {

    BitsVector::BitsVector() {
      this->high = 0;
      this->low  = 0;
    }


    BitsVector::BitsVector(triton::uint32 high, triton::uint32 low) {
      this->high = high;
      this->low  = low;
    }


    BitsVector::BitsVector(const BitsVector &copy) {
      this->high = copy.high;
      this->low  = copy.low;
    }


    BitsVector::~BitsVector() {
    }


    std::pair<triton::uint32, triton::uint32> BitsVector::getPair(void) const {
      return std::make_pair(this->high, this->low);
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


    void BitsVector::setHigh(triton::uint32 v) {
      this->high = v;

      if (this->high > DQWORD_SIZE_BIT)
        throw std::runtime_error("BitsVector::setHigh(): size cannot be greater than a DQWORD.");

      if (this->getVectorSize() % BYTE_SIZE_BIT && this->getVectorSize() != FLAG_SIZE_BIT)
        throw std::runtime_error("BitsVector::setHigh(): the vector size must be a multiple of 8");
    }


    void BitsVector::setLow(triton::uint32 v) {
      this->low = v;

      if (this->low > this->high)
        throw std::runtime_error("BitsVector::setLow(): low cannot be greater than high.");

      if (this->low % BYTE_SIZE_BIT)
        throw std::runtime_error("BitsVector::setLow(): low must be a multiple of 8");
    }


    void BitsVector::setPair(std::pair<triton::uint32, triton::uint32> p) {
      this->high = std::get<0>(p);
      this->low  = std::get<1>(p);

      if (this->high > DQWORD_SIZE_BIT)
        throw std::runtime_error("BitsVector::setPair(): size cannot be greater than a DQWORD.");

      if (this->low % BYTE_SIZE_BIT)
        throw std::runtime_error("BitsVector::setPair(): low must be a multiple of 8");

      if (this->low > this->high)
        throw std::runtime_error("BitsVector::setPair(): low cannot be greater than high.");

      if (this->getVectorSize() % BYTE_SIZE_BIT && this->getVectorSize() != FLAG_SIZE_BIT)
        throw std::runtime_error("BitsVector::setHigh(): the vector size must be a multiple of 8");
    }


    void BitsVector::operator=(const BitsVector& other) {
      this->high = other.high;
      this->low  = other.low;
    }


    std::ostream &operator<<(std::ostream &stream, BitsVector bv) {
      stream << "bv[" << bv.getHigh() << ".." << bv.getLow() << "]";
      return stream;
    }

  }; /* arch namespace */
}; /* triton namespace */
