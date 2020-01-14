//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/armOperandProperties.hpp>
#include <triton/exceptions.hpp>



namespace triton {
  namespace arch {
    namespace arm {

      ArmOperandProperties::ArmOperandProperties() {
        this->extendSize          = 0;
        this->extendType          = triton::arch::arm::ID_EXTEND_INVALID;
        this->shiftType           = triton::arch::arm::ID_SHIFT_INVALID;
        this->shiftValueImmediate = 0;
        this->shiftValueRegister  = triton::arch::ID_REG_INVALID;
        this->subtracted          = false;
      }


      ArmOperandProperties::ArmOperandProperties(const ArmOperandProperties& other) {
        this->extendSize          = other.extendSize;
        this->extendType          = other.extendType;
        this->shiftType           = other.shiftType;
        this->shiftValueImmediate = other.shiftValueImmediate;
        this->shiftValueRegister  = other.shiftValueRegister;
        this->subtracted          = other.subtracted;
      }


      ArmOperandProperties& ArmOperandProperties::operator=(const ArmOperandProperties& other) {
        this->extendSize          = other.extendSize;
        this->extendType          = other.extendType;
        this->shiftType           = other.shiftType;
        this->shiftValueImmediate = other.shiftValueImmediate;
        this->shiftValueRegister  = other.shiftValueRegister;
        this->subtracted          = other.subtracted;
        return *this;
      }


      triton::arch::arm::shift_e ArmOperandProperties::getShiftType(void) const {
        return this->shiftType;
      }


      triton::uint32 ArmOperandProperties::getShiftImmediate(void) const {
        return this->shiftValueImmediate;
      }


      triton::arch::register_e ArmOperandProperties::getShiftRegister(void) const {
        return this->shiftValueRegister;
      }


      triton::arch::arm::extend_e ArmOperandProperties::getExtendType(void) const {
        return this->extendType;
      }


      triton::uint32 ArmOperandProperties::getExtendSize(void) const {
        return this->extendSize;
      }


      bool ArmOperandProperties::getSubtracted(void) const {
        return this->subtracted;
      }


      void ArmOperandProperties::setShiftValue(triton::uint32 imm) {
        this->shiftValueImmediate = imm;
      }


      void ArmOperandProperties::setShiftValue(triton::arch::register_e reg) {
        this->shiftValueRegister = reg;
      }


      void ArmOperandProperties::setShiftType(triton::arch::arm::shift_e type) {
        if (type >= triton::arch::arm::ID_SHIFT_LAST_ITEM)
          throw triton::exceptions::ArmOperandProperties("ArmOperandProperties::setShiftType(): invalid type of shift.");
        this->shiftType = type;
      }


      void ArmOperandProperties::setExtendType(triton::arch::arm::extend_e type) {
        if (type >= triton::arch::arm::ID_EXTEND_LAST_ITEM)
          throw triton::exceptions::ArmOperandProperties("ArmOperandProperties::setExtendType(): invalid type of extend.");
        this->extendType = type;
      }


      void ArmOperandProperties::setExtendedSize(triton::uint32 dstSize) {
        switch (this->extendType) {
          case triton::arch::arm::ID_EXTEND_SXTB:
          case triton::arch::arm::ID_EXTEND_UXTB:
            this->extendSize = dstSize - 8;
            break;

          case triton::arch::arm::ID_EXTEND_SXTH:
          case triton::arch::arm::ID_EXTEND_UXTH:
            this->extendSize = dstSize - 16;
            break;

          case triton::arch::arm::ID_EXTEND_SXTW:
          case triton::arch::arm::ID_EXTEND_UXTW:
            this->extendSize = dstSize - 32;
            break;

          case triton::arch::arm::ID_EXTEND_SXTX:
          case triton::arch::arm::ID_EXTEND_UXTX:
            this->extendSize = dstSize - 64;
            break;

          default:
            throw triton::exceptions::ArmOperandProperties("ArmOperandProperties::setExtendedSize(): invalid type of extend");
        }

        if (this->extendSize > 64)
          throw triton::exceptions::ArmOperandProperties("ArmOperandProperties::setExtendedSize(): invalid size of extension (integer overflow).");

        if (dstSize != 8 && dstSize != 16 && dstSize != 32 && dstSize != 64)
          throw triton::exceptions::ArmOperandProperties("ArmOperandProperties::setExtendedSize(): size must be 8, 16, 32 or 64.");
      }


      void ArmOperandProperties::setSubtracted(bool value) {
        this->subtracted = value;
      }

    }; /* arm namespace */
  }; /* arch namespace */
}; /* triton namespace */
