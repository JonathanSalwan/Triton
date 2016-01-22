//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_IMMEDIATEOPERAND_H
#define TRITON_IMMEDIATEOPERAND_H

#include "bitsVector.hpp"
#include "operandInterface.hpp"
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

    /*! \class ImmediateOperand
     *  \brief This class is used when an instruction has an immediate operand.
     */
    class ImmediateOperand : public BitsVector, public OperandInterface {

      protected:
        //! The operand's value.
        triton::__uint value;

        //! Copy an ImmediateOperand.
        void copy(const ImmediateOperand& other);

      public:
        //! Constructor.
        ImmediateOperand();

        //! Constructor.
        ImmediateOperand(triton::__uint value, triton::uint32 size /* bytes*/);

        //! Constructor by copy.
        ImmediateOperand(const ImmediateOperand& other);

        //! Destructor.
        ~ImmediateOperand();

        //! Returns the operand's value.
        triton::__uint getValue(void) const;

        //! Returns the highest bit. \sa BitsVector::getHigh()
        triton::uint32 getAbstractHigh(void) const;

        //! Returns the lower bit. \sa BitsVector::getLow()
        triton::uint32 getAbstractLow(void) const;

        //! Returns the immediate's size in bits
        triton::uint32 getBitSize(void) const;

        //! Returns the immediate's size in byte
        triton::uint32 getSize(void) const;

        //! Returns the operand's type.
        triton::uint32 getType(void) const;

        //! Sets the operand's value.
        void setValue(triton::__uint v);

        //! Copy an ImmediateOperand.
        void operator=(const ImmediateOperand& other);
    };

    //! Displays an ImmediateOperand.
    std::ostream &operator<<(std::ostream &stream, ImmediateOperand imm);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_IMMEDIATEOPERAND_H */

