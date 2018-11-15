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
      this->extendType = triton::arch::aarch64::ID_EXTEND_INVALID;
      this->shiftType  = triton::arch::aarch64::ID_SHIFT_INVALID;
      this->shiftValue = 0;
    }


    AArch64OperandProperties::AArch64OperandProperties(triton::arch::aarch64::extend_e extendType, triton::arch::aarch64::shift_e shiftType, triton::uint32 shiftValue) {
      this->extendType = extendType;
      this->shiftType  = shiftType;
      this->shiftValue = shiftValue;
    }


    AArch64OperandProperties::AArch64OperandProperties(const AArch64OperandProperties& other) {
      this->extendType = other.extendType;
      this->shiftType  = other.shiftType;
      this->shiftValue = other.shiftValue;
    }


    AArch64OperandProperties& AArch64OperandProperties::operator=(const AArch64OperandProperties& other) {
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

  }; /* arch namespace */
}; /* triton namespace */
