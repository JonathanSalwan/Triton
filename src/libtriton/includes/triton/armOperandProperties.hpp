//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ARMOPERANDPROPERTIES
#define TRITON_ARMOPERANDPROPERTIES

#include <triton/archEnums.hpp>
#include <triton/dllexport.hpp>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The arch namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    //! The arm namespace
    namespace arm {
    /*!
     *  \ingroup arch
     *  \addtogroup arm
     *  @{
     */

      /*! \class ArmOperandProperties
       *  \brief This class is used to represent specific properties of an Arm operand.
       */
      class ArmOperandProperties {
        protected:
          //! The shift type.
          triton::arch::arm::shift_e shiftType;

          //! The shift value immediate.
          triton::uint32 shiftValueImmediate;

          //! The shift value register.
          triton::arch::register_e shiftValueRegister;

          //! The extend type.
          triton::arch::arm::extend_e extendType;

          //! The extend size (in bits).
          triton::uint32 extendSize;

          //! The subtracted flag. Used in memory access operands and determines whether this operand has to be added or subtracted to the base register.
          bool subtracted;
        public:
          //! Constructor.
          TRITON_EXPORT ArmOperandProperties();

          //! Constructor by copy.
          TRITON_EXPORT ArmOperandProperties(const ArmOperandProperties& other);

          //! Returns the type of the shift.
          TRITON_EXPORT triton::arch::arm::shift_e getShiftType(void) const;

          //! Returns the value of the shift immediate.
          TRITON_EXPORT triton::uint32 getShiftImmediate(void) const;

          //! Returns the value of the shift register.
          TRITON_EXPORT triton::arch::register_e getShiftRegister(void) const;

          //! Returns the type of the extend.
          TRITON_EXPORT triton::arch::arm::extend_e getExtendType(void) const;

          //! Returns the size (in bits) of the extend.
          TRITON_EXPORT triton::uint32 getExtendSize(void) const;

          //! Returns true if the operand has to be subtracted when computing a memory access.
          TRITON_EXPORT bool isSubtracted(void) const;

          //! Sets the type of the shift.
          TRITON_EXPORT void setShiftType(triton::arch::arm::shift_e type);

          //! Sets the value of the shift immediate.
          TRITON_EXPORT void setShiftValue(triton::uint32 imm);

          //! Sets the value of the shift register.
          TRITON_EXPORT void setShiftValue(triton::arch::register_e reg);

          //! Sets the type of the extend.
          TRITON_EXPORT void setExtendType(triton::arch::arm::extend_e type);

          //! Sets the extended size (in bits) after extension.
          TRITON_EXPORT void setExtendedSize(triton::uint32 dstSize);

          //! Sets subtracted flag.
          TRITON_EXPORT void setSubtracted(bool value);

          //! Copy an ArmOperandProperties.
          TRITON_EXPORT ArmOperandProperties& operator=(const ArmOperandProperties& other);
      };

    /*! @} End of arm namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ARMOPERANDPROPERTIES */
