//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/armOperandProperties.hpp>
#include <triton/cpuSize.hpp>
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
        this->vasType             = triton::arch::arm::ID_VAS_INVALID;
        this->vectorIndex         = -1;
      }


      ArmOperandProperties::ArmOperandProperties(const ArmOperandProperties& other) {
        this->extendSize          = other.extendSize;
        this->extendType          = other.extendType;
        this->shiftType           = other.shiftType;
        this->shiftValueImmediate = other.shiftValueImmediate;
        this->shiftValueRegister  = other.shiftValueRegister;
        this->subtracted          = other.subtracted;
        this->vasType             = other.vasType;
        this->vectorIndex         = other.vectorIndex;
      }


      ArmOperandProperties& ArmOperandProperties::operator=(const ArmOperandProperties& other) {
        this->extendSize          = other.extendSize;
        this->extendType          = other.extendType;
        this->shiftType           = other.shiftType;
        this->shiftValueImmediate = other.shiftValueImmediate;
        this->shiftValueRegister  = other.shiftValueRegister;
        this->subtracted          = other.subtracted;
        this->vasType             = other.vasType;
        this->vectorIndex         = other.vectorIndex;
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


      triton::arch::arm::vas_e ArmOperandProperties::getVASType(void) const {
        return this->vasType;
      }


      triton::sint32 ArmOperandProperties::getVectorIndex(void) const {
        return this->vectorIndex;
      }


      std::string ArmOperandProperties::getVASName(void) const {
        switch (this->vasType) {
          case ID_VAS_16B: return "16B";
          case ID_VAS_8B:  return "8B";
          case ID_VAS_8H:  return "8H";
          case ID_VAS_4H:  return "4H";
          case ID_VAS_4S:  return "4S";
          case ID_VAS_2S:  return "2S";
          case ID_VAS_2D:  return "2D";
          case ID_VAS_1D:  return "1D";
          default:         return "invalid";
        }
      }


      triton::uint32 ArmOperandProperties::getVASSize(void) const {
        switch (this->vasType) {
          case ID_VAS_16B: return triton::size::dqword;
          case ID_VAS_8H:  return triton::size::dqword;
          case ID_VAS_4S:  return triton::size::dqword;
          case ID_VAS_2D:  return triton::size::dqword;
          case ID_VAS_8B:  return triton::size::qword;
          case ID_VAS_4H:  return triton::size::qword;
          case ID_VAS_2S:  return triton::size::qword;
          case ID_VAS_1D:  return triton::size::qword;
          default:         return 0;
        }
      }


      triton::uint32 ArmOperandProperties::getExtendSize(void) const {
        return this->extendSize;
      }


      bool ArmOperandProperties::isSubtracted(void) const {
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


      void ArmOperandProperties::setVASType(triton::arch::arm::vas_e type) {
        if (type >= triton::arch::arm::ID_VAS_LAST_ITEM)
          throw triton::exceptions::ArmOperandProperties("ArmOperandProperties::setVASType(): invalid type of VAS.");
        this->vasType = type;
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


      void ArmOperandProperties::setVectorIndex(triton::sint32 index) {
        this->vectorIndex = index;
      }

    }; /* arm namespace */
  }; /* arch namespace */
}; /* triton namespace */
