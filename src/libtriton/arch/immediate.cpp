//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/immediate.hpp>
#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/softfloat.hpp>
#include <triton/coreUtils.hpp>

#ifdef LITTLE_ENDIAN // provided by CMake
constexpr auto sys_endianness = triton::arch::LE_ENDIANNESS;
#else
constexpr auto sys_endianness = triton::arch::BE_ENDIANNESS;
#endif


namespace triton {
  namespace arch {

    Immediate::Immediate() {
      this->value = 0;
    }


    Immediate::Immediate(triton::uint64 value, triton::uint32 size /* bytes */) {
      this->setValue(value, size);
    }


    Immediate::Immediate(double value, triton::uint32 size /* bytes */, triton::arch::endianness_e platform_endianness) {
      triton::uint64 imm_value;
      auto need_swap = sys_endianness != platform_endianness;

      if (size == sizeof(double)) {
        static_assert(sizeof(double) == sizeof(triton::uint64), "Unexpected double type size");
        std::memcpy(&imm_value, &value, sizeof(double));
        if (need_swap) {
          imm_value = utils::byteswap(imm_value);
        }
      }

      else if (size == sizeof(float)) { // single-precision
        float fvalue = static_cast<float>(value);
        triton::uint32 repr;
        static_assert(sizeof(float) == sizeof(uint32_t), "Unexpected float type size");
        std::memcpy(&repr, &fvalue, sizeof(float));
        imm_value = need_swap ? static_cast<triton::uint64>(utils::byteswap(repr)) : static_cast<triton::uint64>(repr);
      }

      else if (size == 2) { // half-precision
        float fvalue = static_cast<float>(value);
        triton::uint16 repr = triton::sf::f32_to_f16(fvalue);
        imm_value = need_swap ? static_cast<triton::uint64>(utils::byteswap(repr)) : static_cast<triton::uint64>(repr);
      }

      else {
        throw triton::exceptions::Immediate("Immediate::Immediate(double): Invalid encoding size.");
      }

      this->setValue(imm_value, size);
    }


    Immediate::Immediate(const Immediate& other)
      : BitsVector(other),
        ArmOperandProperties(other) {
      this->copy(other);
    }


    triton::uint64 Immediate::getValue(void) const {
      return this->value;
    }


    void Immediate::setValue(triton::uint64 value, triton::uint32 size /* bytes */) {
      /* If the size is zero, try to define the size according to the value. */
      if (size == 0) {
        if      (/* ..... 0x0000000000000000 */ value <= 0x00000000000000ff) size = triton::size::byte;
        else if (value >= 0x0000000000000100 && value <= 0x000000000000ffff) size = triton::size::word;
        else if (value >= 0x0000000000010000 && value <= 0x00000000ffffffff) size = triton::size::dword;
        else if (value >= 0x0000000100000000 && value <= 0xffffffffffffffff) size = triton::size::qword;
      }

      if (size != triton::size::byte     &&
          size != triton::size::word     &&
          size != triton::size::dword    &&
          size != triton::size::qword    &&
          size != triton::size::fword    &&
          size != triton::size::dqword   &&
          size != triton::size::qqword   &&
          size != triton::size::dqqword)
        throw triton::exceptions::Immediate("Immediate::setValue(): size must be aligned.");

      switch (size) {
        case triton::size::byte:
          this->value = static_cast<triton::uint8>(value);
          break;

        case triton::size::word:
          this->value = static_cast<triton::uint16>(value);
          break;

        case triton::size::dword:
          this->value = static_cast<triton::uint32>(value);
          break;

        /* In most CPU cases, integers more than 64 are loaded from memory */
        default:
          this->value = value;
      }

      this->setBits(((size * triton::bitsize::byte) - 1), 0);
    }


    triton::uint32 Immediate::getSize(void) const {
      return this->getVectorSize() / triton::bitsize::byte;
    }


    triton::uint32 Immediate::getBitSize(void) const {
      return this->getVectorSize();
    }


    triton::arch::operand_e Immediate::getType(void) const {
      return triton::arch::OP_IMM;
    }


    Immediate& Immediate::operator=(const Immediate& other) {
      ArmOperandProperties::operator=(other);
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
