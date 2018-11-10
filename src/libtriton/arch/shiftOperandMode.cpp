//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/aarch64Specifications.hpp>
#include <triton/exceptions.hpp>
#include <triton/shiftOperandMode.hpp>



namespace triton {
  namespace arch {

    ShiftOperandMode::ShiftOperandMode() {
      this->type  = 0;
      this->value = 0;
    }


    ShiftOperandMode::ShiftOperandMode(triton::uint32 type, triton::uint64 value) {
      this->type  = type;
      this->value = value;
    }


    ShiftOperandMode::ShiftOperandMode(const ShiftOperandMode& other) {
      this->type  = other.type;
      this->value = other.value;
    }


    ShiftOperandMode& ShiftOperandMode::operator=(const ShiftOperandMode& other) {
      this->type  = other.type;
      this->value = other.value;
      return *this;
    }


    triton::uint64 ShiftOperandMode::getShiftValue(void) const {
      return this->value;
    }


    triton::uint32 ShiftOperandMode::getShiftType(void) const {
      return this->type;
    }


    void ShiftOperandMode::setShiftValue(triton::uint64 value) {
      this->value = value;
    }


    void ShiftOperandMode::setShiftType(triton::uint32 type) {
      if (type >= triton::arch::aarch64::ID_SHIFT_LAST_ITEM)
        throw triton::exceptions::ShiftOperandMode("ShiftOperandMode::setShiftType(): invalid type of shift.");
      this->type = type;
    }

  }; /* arch namespace */
}; /* triton namespace */
