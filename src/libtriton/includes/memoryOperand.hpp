//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_MEMORYOPERAND
#define TRITON_MEMORYOPERAND

#include "ast.hpp"
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
        triton::uint512 concreteValue;

        //! True if this concrete memory value is trusted and synchronized with the real MMU value.
        bool trusted;

        //! Contains the pc relative if it exists.
        triton::__uint pcRelative;

        //! LEA - If the operand has a segment register, this attribute is filled.
        RegisterOperand segmentReg;

        //! LEA - If the operand has a base register, this attribute is filled.
        RegisterOperand baseReg;

        //! LEA - If the operand has an index register, this attribute is filled.
        RegisterOperand indexReg;

        //! LEA - If the operand has a displacement, this attribute is filled.
        ImmediateOperand displacement;

        //! LEA - If the operand has a scale, this attribute is filled.
        ImmediateOperand scale;

        //! The AST of the memory access.
        triton::ast::AbstractNode* ast;

        //! Copy a MemoryOperand.
        void copy(const MemoryOperand& other);

      public:
        //! Constructor.
        MemoryOperand();

        //! Constructor.
        MemoryOperand(triton::__uint address, triton::uint32 size /* bytes */, triton::uint512 concreteValue=0);

        //! Constructor by copy.
        MemoryOperand(const MemoryOperand& other);

        //! Destructor.
        ~MemoryOperand();

        //! Initialize the address of the memory.
        void initAddress(void);

        //! Returns the AST of the memory access (LEA).
        triton::ast::AbstractNode* getLeaAst(void) const;

        //! Returns the address of the memory.
        triton::__uint getAddress(void) const;

        //! Returns the highest bit of the memory vector. \saa BitsVector::getHigh()
        triton::uint32 getAbstractHigh(void) const;

        //! Returns the lower bit of the memory vector. \sa BitsVector::getLow()
        triton::uint32 getAbstractLow(void) const;

        //! Returns the size (in bits) of the memory vector.
        triton::uint32 getBitSize(void) const;

        //! Returnts the concrete value (content of the access)
        triton::uint512 getConcreteValue(void) const;

        //! LEA - Gets pc relative.
        triton::__uint getPcRelative(void) const;

        //! Returns the size (in bytes) of the memory vector.
        triton::uint32 getSize(void) const;

        //! Returns the type of the operand (triton::arch::OP_MEM).
        triton::uint32 getType(void) const;

        //! LEA - Returns the segment register operand.
        RegisterOperand& getSegmentRegister(void);

        //! LEA - Returns the base register operand.
        RegisterOperand& getBaseRegister(void);

        //! LEA - Returns the index register operand.
        RegisterOperand& getIndexRegister(void);

        //! LEA - Returns the displacement operand.
        ImmediateOperand& getDisplacement(void);

        //! LEA - Returns the scale operand.
        ImmediateOperand& getScale(void);

        //! LEA - Returns the segment register operand.
        const RegisterOperand& getConstSegmentRegister(void) const;

        //! LEA - Returns the base register operand.
        const RegisterOperand& getConstBaseRegister(void) const;

        //! LEA - Returns the index register operand.
        const RegisterOperand& getConstIndexRegister(void) const;

        //! LEA - Returns the displacement operand.
        const ImmediateOperand& getConstDisplacement(void) const;

        //! LEA - Returns the scale operand.
        const ImmediateOperand& getConstScale(void) const;

        //! True if this concrete memory value is trusted and synchronized with the real MMU value.
        bool isTrusted(void) const;

        //! True if the memory is not empty.
        bool isValid(void) const;

        //! Sets the trust flag.
        void setTrust(bool flag);

        //! Sets the address of the memory access.
        void setAddress(triton::__uint addr);

        //! Sets the concrete value of the memory access.
        void setConcreteValue(triton::uint512 concreteValue);

        //! LEA - Sets pc relative.
        void setPcRelative(triton::__uint addr);

        //! LEA - Sets the segment register operand.
        void setSegmentRegister(RegisterOperand& segment);

        //! LEA - Sets the base register operand.
        void setBaseRegister(RegisterOperand& base);

        //! LEA - Sets the index register operand.
        void setIndexRegister(RegisterOperand& index);

        //! LEA - Sets the displacement operand.
        void setDisplacement(ImmediateOperand& displacement);

        //! LEA - Sets the scale operand.
        void setScale(ImmediateOperand& scale);

        //! Copies a MemoryOperand.
        void operator=(const MemoryOperand& other);
   };

    //! Displays an MemoryOperand.
    std::ostream& operator<<(std::ostream& stream, const MemoryOperand& mem);

    //! Displays an MemoryOperand.
    std::ostream& operator<<(std::ostream& stream, const MemoryOperand* mem);

    //! Compares two MemoryOperand.
    bool operator==(const MemoryOperand& mem1, const MemoryOperand& mem2);

    //! Compares two MemoryOperand.
    bool operator!=(const MemoryOperand& mem1, const MemoryOperand& mem2);

    //! Compares two MemoryOperand (needed for std::map)
    bool operator<(const MemoryOperand& mem1, const MemoryOperand& mem2);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif     /* !MEMORYOPERAND */

