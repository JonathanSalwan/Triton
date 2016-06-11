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
        //! The value of the operand.
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

        //! Returns the value of the operand.
        triton::__uint getValue(void) const;

        //! Returns the highest bit. \sa BitsVector::getHigh()
        triton::uint32 getAbstractHigh(void) const;

        //! Returns the lower bit. \sa BitsVector::getLow()
        triton::uint32 getAbstractLow(void) const;

        //! Returns the size (in bits) of the immediate vector.
        triton::uint32 getBitSize(void) const;

        //! Returns the size (in bytes) of the immediate vector.
        triton::uint32 getSize(void) const;

        //! Returns the type of the operand (triton::arch::OP_IMM).
        triton::uint32 getType(void) const;

        //! Sets the value of the operand.
        void setValue(triton::__uint v);

        //! Copy an ImmediateOperand.
        void operator=(const ImmediateOperand& other);
    };

    //! Displays an ImmediateOperand.
    std::ostream& operator<<(std::ostream& stream, const ImmediateOperand& imm);

    //! Displays an ImmediateOperand.
    std::ostream& operator<<(std::ostream& stream, const ImmediateOperand* imm);

    //! Compares two ImmediateOperand.
    bool operator==(const ImmediateOperand& imm1, const ImmediateOperand& imm2);

    //! Compares two ImmediateOperand.
    bool operator!=(const ImmediateOperand& imm1, const ImmediateOperand& imm2);

    //! Compares two ImmediateOperand (needed for std::map)
    bool operator<(const ImmediateOperand& imm1, const ImmediateOperand& imm2);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_IMMEDIATEOPERAND_H */

