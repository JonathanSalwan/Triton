//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/immediate.hpp>



namespace triton {
  namespace arch {

    Immediate::Immediate() {
      this->value = 0;
    }


    Immediate::Immediate(triton::uint64 value, triton::uint32 size /* bytes */) {
      this->setValue(value, size);
    }


    Immediate::Immediate(const Immediate& other)
      : BitsVector(other), AArch64OperandProperties(other) {
      this->copy(other);
    }


    triton::uint64 Immediate::getValue(void) const {
      return this->value;
    }


    void Immediate::setValue(triton::uint64 value, triton::uint32 size /* bytes */) {
      /* If the size is zero, try to define the size according to the value. */
      if (size == 0) {
        if      (/* ..... 0x0000000000000000 */ value <= 0x00000000000000ff) size = BYTE_SIZE;
        else if (value >= 0x0000000000000100 && value <= 0x000000000000ffff) size = WORD_SIZE;
        else if (value >= 0x0000000000010000 && value <= 0x00000000ffffffff) size = DWORD_SIZE;
        else if (value >= 0x0000000100000000 && value <= 0xffffffffffffffff) size = QWORD_SIZE;
      }

      if (size != BYTE_SIZE     &&
          size != WORD_SIZE     &&
          size != DWORD_SIZE    &&
          size != QWORD_SIZE    &&
          size != DQWORD_SIZE   &&
          size != QQWORD_SIZE   &&
          size != DQQWORD_SIZE)
        throw triton::exceptions::Immediate("Immediate::setValue(): size must be aligned.");

      switch (size) {
        case BYTE_SIZE:
          this->value = static_cast<triton::uint8>(value);
          break;

        case WORD_SIZE:
          this->value = static_cast<triton::uint16>(value);
          break;

        case DWORD_SIZE:
          this->value = static_cast<triton::uint32>(value);
          break;

        /* In most CPU cases, integers more than 64 are loaded from memory */
        default:
          this->value = value;
      }

      this->setPair(std::make_pair(((size * BYTE_SIZE_BIT) - 1), 0));
    }


    triton::uint32 Immediate::getSize(void) const {
      return this->getVectorSize() / BYTE_SIZE_BIT;
    }


    triton::uint32 Immediate::getBitSize(void) const {
      return this->getVectorSize();
    }


    triton::arch::operand_e Immediate::getType(void) const {
      return triton::arch::OP_IMM;
    }


    Immediate& Immediate::operator=(const Immediate& other) {
      AArch64OperandProperties::operator=(other);
      BitsVector::operator=(other);
      this->copy(other);
      return *this;
    }


    void Immediate::copy(const Immediate& other) {
      this->value = other.value;
    }


    std::ostream& operator<<(std::ostream& stream, const Immediate& imm) {
      stream << "0x"
             << std::hex << imm.getValue()
             << ":"
             << std::dec << imm.getBitSize()
             << " bv["
             << imm.getHigh()
             << ".."
             << imm.getLow()
             << "]";
      return stream;
    }


    std::ostream& operator<<(std::ostream& stream, const Immediate* imm) {
      stream << *imm;
      return stream;
    }


    bool operator==(const Immediate& imm1, const Immediate& imm2) {
      if (imm1.getValue() != imm2.getValue())
        return false;
      if (imm1.getSize() != imm2.getSize())
        return false;
      return true;
    }


    bool operator!=(const Immediate& imm1, const Immediate& imm2) {
      return !(imm1 == imm2);
    }


    bool operator<(const Immediate& imm1, const Immediate& imm2) {
      triton::uint64 seed1 = 0;
      triton::uint64 seed2 = 0;

      /*
       * Golden ratio 32-bits -> 0x9e3779b9
       * Golden ratio 64-bits -> 0x9e3779b97f4a7c13
       */
      seed1 ^= imm1.getValue() + 0x9e3779b97f4a7c13 + (seed1 << 6) + (seed1 >> 2);
      seed1 ^= imm1.getSize() + 0x9e3779b97f4a7c13 + (seed1 << 6) + (seed1 >> 2);

      seed2 ^= imm2.getValue() + 0x9e3779b97f4a7c13 + (seed2 << 6) + (seed2 >> 2);
      seed2 ^= imm2.getSize() + 0x9e3779b97f4a7c13 + (seed2 << 6) + (seed2 >> 2);

      return (seed1 < seed2);
    }

  }; /* arch namespace */
}; /* triton namespace */
