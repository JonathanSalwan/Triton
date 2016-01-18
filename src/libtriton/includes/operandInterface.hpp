//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_OPERANDINTERFACE_H
#define TRITON_OPERANDINTERFACE_H

#include "tritonTypes.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Triton namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    //! Operand's type
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

        //! Returns the operand's size (in bit).
        virtual triton::uint32 getBitSize(void) const = 0;

        //! Returns the operand's size (in byte).
        virtual triton::uint32 getSize(void) const = 0;

        //! Returns the operand's highest bit.
        /*! \sa BitsVector::getHigh() */
        virtual triton::uint32 getAbstractHigh(void) const = 0;

        //! Returns the operand's lower bit.
        /*! \sa BitsVector::getLow() */
        virtual triton::uint32 getAbstractLow(void) const = 0;

        //! Returns the operand's type (Imm, Mem, Reg).
        virtual triton::uint32 getType(void) const = 0;

    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_OPERANDINTERFACE_H */

