//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_IMMEDIATE_H
#define TRITON_IMMEDIATE_H

#include <triton/bitsVector.hpp>
#include <triton/operandInterface.hpp>
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

    /*! \class Immediate
     *  \brief This class is used to represent an immediate.
     */
    class Immediate : public BitsVector, public OperandInterface {

      protected:
        //! The value of the operand.
        triton::uint64 value;

        //! Copy an Immediate.
        void copy(const Immediate& other);

      public:
        //! Constructor.
        Immediate();

        //! Constructor.
        Immediate(triton::uint64 value, triton::uint32 size /* bytes*/);

        //! Constructor by copy.
        Immediate(const Immediate& other);

        //! Destructor.
        virtual ~Immediate();

        //! Returns the value of the operand.
        triton::uint64 getValue(void) const;

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
        void setValue(triton::uint64 v);

        //! Copy an Immediate.
        void operator=(const Immediate& other);
    };

    //! Displays an Immediate.
    std::ostream& operator<<(std::ostream& stream, const Immediate& imm);

    //! Displays an Immediate.
    std::ostream& operator<<(std::ostream& stream, const Immediate* imm);

    //! Compares two Immediate.
    bool operator==(const Immediate& imm1, const Immediate& imm2);

    //! Compares two Immediate.
    bool operator!=(const Immediate& imm1, const Immediate& imm2);

    //! Compares two Immediate (needed for std::map)
    bool operator<(const Immediate& imm1, const Immediate& imm2);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_IMMEDIATE_H */
