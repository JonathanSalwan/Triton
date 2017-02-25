//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_OPERANDINTERFACE_H
#define TRITON_OPERANDINTERFACE_H

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

    //! Type Operand
    enum operandType_e {
      OP_INVALID = 0, //!< invalid operand
      OP_IMM,         //!< immediate operand
      OP_MEM,         //!< memory operand
      OP_REG          //!< register operand
    };

    /*! \interface OperandInterface
     *  \brief This interface is used for instruction operands.
     */
    class OperandInterface {

      public:
        //! Destructor.
        virtual ~OperandInterface() {};

        //! Returns the size (in bits) of the operand.
        virtual triton::uint32 getBitSize(void) const = 0;

        //! Returns the size (in bytes) of the operand.
        virtual triton::uint32 getSize(void) const = 0;

        //! Returns the highest bit of the operand vector.
        /*! \sa BitsVector::getHigh() */
        virtual triton::uint32 getAbstractHigh(void) const = 0;

        //! Returns the lower bit of the operand vector.
        /*! \sa BitsVector::getLow() */
        virtual triton::uint32 getAbstractLow(void) const = 0;

        //! Returns the type of the operand (`Imm`, `Mem`, `Reg`).
        virtual triton::uint32 getType(void) const = 0;
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_OPERANDINTERFACE_H */

