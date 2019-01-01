//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/aarch64OperandProperties.hpp>
#include <triton/aarch64Specifications.hpp>
#include <triton/exceptions.hpp>



namespace triton {
  namespace arch {

    AArch64OperandProperties::AArch64OperandProperties() {
      this->extendSize = 0;
      this->extendType = triton::arch::aarch64::ID_EXTEND_INVALID;
      this->shiftType  = triton::arch::aarch64::ID_SHIFT_INVALID;
      this->shiftValue = 0;
    }


    AArch64OperandProperties::AArch64OperandProperties(const AArch64OperandProperties& other) {
      this->extendSize = other.extendSize;
      this->extendType = other.extendType;
      this->shiftType  = other.shiftType;
      this->shiftValue = other.shiftValue;
    }


    AArch64OperandProperties& AArch64OperandProperties::operator=(const AArch64OperandProperties& other) {
      this->extendSize = other.extendSize;
      this->extendType = other.extendType;
      this->shiftType  = other.shiftType;
      this->shiftValue = other.shiftValue;
      return *this;
    }


    triton::uint32 AArch64OperandProperties::getShiftValue(void) const {
      return this->shiftValue;
    }


    triton::arch::aarch64::shift_e AArch64OperandProperties::getShiftType(void) const {
      return this->shiftType;
    }


    triton::arch::aarch64::extend_e AArch64OperandProperties::getExtendType(void) const {
      return this->extendType;
    }


    triton::uint32 AArch64OperandProperties::getExtendSize(void) const {
      return this->extendSize;
    }


    void AArch64OperandProperties::setShiftValue(triton::uint32 value) {
      this->shiftValue = value;
    }


    void AArch64OperandProperties::setShiftType(triton::arch::aarch64::shift_e type) {
      if (type >= triton::arch::aarch64::ID_SHIFT_LAST_ITEM)
        throw triton::exceptions::AArch64OperandProperties("AArch64OperandProperties::setShiftType(): invalid type of shift.");
      this->shiftType = type;
    }


    void AArch64OperandProperties::setExtendType(triton::arch::aarch64::extend_e type) {
      if (type >= triton::arch::aarch64::ID_EXTEND_LAST_ITEM)
        throw triton::exceptions::AArch64OperandProperties("AArch64OperandProperties::setExtendType(): invalid type of extend.");
      this->extendType = type;
    }


    void AArch64OperandProperties::setExtendedSize(triton::uint32 dstSize) {
      switch (this->extendType) {
        case triton::arch::aarch64::ID_EXTEND_SXTB:
        case triton::arch::aarch64::ID_EXTEND_UXTB:
          this->extendSize = dstSize - 8;
          break;

        case triton::arch::aarch64::ID_EXTEND_SXTH:
        case triton::arch::aarch64::ID_EXTEND_UXTH:
          this->extendSize = dstSize - 16;
          break;

        case triton::arch::aarch64::ID_EXTEND_SXTW:
        case triton::arch::aarch64::ID_EXTEND_UXTW:
          this->extendSize = dstSize - 32;
          break;

        case triton::arch::aarch64::ID_EXTEND_SXTX:
        case triton::arch::aarch64::ID_EXTEND_UXTX:
          this->extendSize = dstSize - 64;
          break;

        default:
          throw triton::exceptions::AArch64OperandProperties("AArch64OperandProperties::setExtendedSize(): invalid type of extend");
      }

      if (this->extendSize > 64)
        throw triton::exceptions::AArch64OperandProperties("AArch64OperandProperties::setExtendedSize(): invalid size of extension (integer overflow).");

      if (dstSize != 8 && dstSize != 16 && dstSize != 32 && dstSize != 64)
        throw triton::exceptions::AArch64OperandProperties("AArch64OperandProperties::setExtendedSize(): size must be 8, 16, 32 or 64.");
    }

  }; /* arch namespace */
}; /* triton namespace */
