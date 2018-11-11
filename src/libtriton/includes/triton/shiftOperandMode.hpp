//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SHIFTOPERANDMODE_H
#define TRITON_SHIFTOPERANDMODE_H

#include <triton/archEnums.hpp>
#include <triton/dllexport.hpp>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Triton namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    /*! \class ShiftOperandMode
     *  \brief This class is used to represent a shift operand mode. Mainly used for AArch64.
     */
    class ShiftOperandMode {
      protected:
        //! The shift type.
        triton::arch::aarch64::shift_e type;

        //! The shift value.
        triton::uint32 value;

      public:
        //! Constructor.
        TRITON_EXPORT ShiftOperandMode();

        //! Constructor.
        TRITON_EXPORT ShiftOperandMode(triton::arch::aarch64::shift_e type, triton::uint32 value);

        //! Constructor by copy.
        TRITON_EXPORT ShiftOperandMode(const ShiftOperandMode& other);

        //! Returns the type of the shift.
        TRITON_EXPORT triton::arch::aarch64::shift_e getShiftType(void) const;

        //! Returns the value of the shift.
        TRITON_EXPORT triton::uint32 getShiftValue(void) const;

        //! Sets the type of the shift.
        TRITON_EXPORT void setShiftType(triton::arch::aarch64::shift_e type);

        //! Sets the value of the shift.
        TRITON_EXPORT void setShiftValue(triton::uint32 value);

        //! Copy an ShiftOperandMode.
        TRITON_EXPORT ShiftOperandMode& operator=(const ShiftOperandMode& other);
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SHIFTOPERANDMODE_H */
