//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SHIFTOPERANDMODE_H
#define TRITON_SHIFTOPERANDMODE_H

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
        //! The shift type. \sa triton::arch::aarch64::shifts_e
        triton::uint32 type;

        //! The shift value.
        triton::uint64 value;

      public:
        //! Constructor.
        TRITON_EXPORT ShiftOperandMode();

        //! Constructor.
        TRITON_EXPORT ShiftOperandMode(triton::uint32 type, triton::uint64 value);

        //! Constructor by copy.
        TRITON_EXPORT ShiftOperandMode(const ShiftOperandMode& other);

        //! Returns the value of the shift.
        TRITON_EXPORT triton::uint64 getShiftValue(void) const;

        //! Returns the type of the shift (triton::arch::aarch64::shifts_s).
        TRITON_EXPORT triton::uint32 getShiftType(void) const;

        //! Sets the value of the shift.
        TRITON_EXPORT void setShiftValue(triton::uint64 value);

        //! Sets the type of the shift.
        TRITON_EXPORT void setShiftType(triton::uint32 type);

        //! Copy an ShiftOperandMode.
        TRITON_EXPORT ShiftOperandMode& operator=(const ShiftOperandMode& other);
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SHIFTOPERANDMODE_H */
