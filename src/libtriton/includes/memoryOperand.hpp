//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_MEMORYOPERAND
#define TRITON_MEMORYOPERAND

#include "bitsVector.hpp"
#include "cpuSize.hpp"
#include "immediateOperand.hpp"
#include "operandInterface.hpp"
#include "registerOperand.hpp"
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

    /*! \class MemoryOperand
     *  \brief This class is used when an instruction has a memory operand.
     */
    class MemoryOperand : public BitsVector, public OperandInterface {

      protected:
        //! The memory' address.
        triton::__uint address;

        //! The concrete value (content of the access)
        triton::uint128 concreteValue;

        //! True if this concrete memory value is trusted and synchronized with the real MMU value.
        bool trusted;

        //! Contains the pc relative if it exists.
        triton::__uint pcRelative;

        //! LEA - If the operand has a base register, this attribute is filled.
        RegisterOperand baseReg;

        //! LEA - If the operand has an index register, this attribute is filled.
        RegisterOperand indexReg;

        //! LEA - If the operand has a displacement, this attribute is filled.
        ImmediateOperand displacement;

        //! LEA - If the operand has a scale, this attribute is filled.
        ImmediateOperand scale;

        //! Copy a MemoryOperand.
        void copy(const MemoryOperand& other);

      public:
        //! Constructor.
        MemoryOperand();

        //! Constructor.
        MemoryOperand(triton::__uint address, triton::uint32 size /* bytes */, triton::uint128 concreteValue=0);

        //! Constructor by copy.
        MemoryOperand(const MemoryOperand& other);

        //! Destructor.
        ~MemoryOperand();

        //! Returns the memory's address.
        triton::__uint getAddress(void) const;

        //! Returns the memory's highest bit. \sa BitsVector::getHigh()
        triton::uint32 getAbstractHigh(void) const;

        //! Returns the memory's lower bit. \sa BitsVector::getLow()
        triton::uint32 getAbstractLow(void) const;

        //! Returns the memory's size (in bit).
        triton::uint32 getBitSize(void) const;

        //! Returnts the concrete value (content of the access)
        triton::uint128 getConcreteValue(void) const;

        //! LEA - Gets pc relative.
        triton::__uint getPcRelative(void) const;

        //! Returns the memory's size (in byte).
        triton::uint32 getSize(void) const;

        //! Returns the operand's type.
        triton::uint32 getType(void) const;

        //! LEA - Returns the base register operand.
        RegisterOperand& getBaseReg(void);

        //! LEA - Returns the index register operand.
        RegisterOperand& getIndexReg(void);

        //! LEA - Returns the displacement operand.
        ImmediateOperand& getDisplacement(void);

        //! LEA - Returns the scale operand.
        ImmediateOperand& getScale(void);

        //! True if this concrete memory value is trusted and synchronized with the real MMU value.
        bool isTrusted(void);

        //! True if the memory is not empty.
        bool isValid(void);

        //! Sets the trust flag.
        void setTrust(bool flag);

        //! Sets the memory's address.
        void setAddress(triton::__uint addr);

        //! Sets the memory's concrete value.
        void setConcreteValue(triton::uint128 concreteValue);

        //! LEA - Sets pc relative.
        void setPcRelative(triton::__uint addr);

        //! LEA - Sets the base register operand.
        void setBaseReg(RegisterOperand base);

        //! LEA - Sets the index register operand.
        void setIndexReg(RegisterOperand index);

        //! LEA - Sets the displacement operand.
        void setDisplacement(ImmediateOperand displacement);

        //! LEA - Sets the scale operand.
        void setScale(ImmediateOperand scale);

        //! Copies a MemoryOperand.
        void operator=(const MemoryOperand& other);

   };

    //! Displays an MemoryOperand.
    std::ostream &operator<<(std::ostream &stream, MemoryOperand mem);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif     /* !MEMORYOPERAND */

