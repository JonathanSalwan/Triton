//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_MEMORYACCESS
#define TRITON_MEMORYACCESS

#include "ast.hpp"
#include "bitsVector.hpp"
#include "cpuSize.hpp"
#include "immediate.hpp"
#include "operandInterface.hpp"
#include "register.hpp"
#include "tritonTypes.hpp"



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  namespace engines {
    namespace symbolic {
      class SymbolicEngine;
    }
  }

  //! The Triton namespace
  namespace arch {
    class CpuInterface;
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    /*! \class MemoryAccess
     *  \brief This class is used to represent a memory access.
     */
    class MemoryAccess : public BitsVector, public OperandInterface {

      protected:
        //! The memory' address.
        triton::uint64 address;

        //! The concrete value (content of the access)
        triton::uint512 concreteValue;

        //! True if this memory contains a concrete value.
        bool concreteValueDefined;

        //! Contains the pc relative if it exists.
        triton::uint64 pcRelative;

        //! LEA - If the operand has a segment register, this attribute is filled.
        triton::arch::Register segmentReg;

        //! LEA - If the operand has a base register, this attribute is filled.
        triton::arch::Register baseReg;

        //! LEA - If the operand has an index register, this attribute is filled.
        triton::arch::Register indexReg;

        //! LEA - If the operand has a displacement, this attribute is filled.
        triton::arch::Immediate displacement;

        //! LEA - If the operand has a scale, this attribute is filled.
        triton::arch::Immediate scale;

        //! The AST of the memory access.
        triton::ast::AbstractNode* ast;

        //! Copy a MemoryAccess.
        void copy(const MemoryAccess& other);

      private:
        //! LEA - Returns the segment register value.
        triton::uint64 getSegmentValue(triton::arch::CpuInterface& cpu);

        //! LEA - Returns the scale immediate value.
        triton::uint64 getScaleValue(void);

        //! LEA - Returns the displacement immediate value.
        triton::uint64 getDisplacementValue(void);

        //! LEA - Returns the size of the memory access.
        triton::uint32 getAccessSize(triton::arch::CpuInterface&);

      public:
        //! Constructor.
        MemoryAccess(triton::arch::CpuInterface const& cpu);

        //! Constructor.
        MemoryAccess(triton::arch::CpuInterface const& cpu, triton::uint64 address, triton::uint32 size /* bytes */);

        //! Constructor.
        MemoryAccess(triton::arch::CpuInterface const& cpu, triton::uint64 address, triton::uint32 size /* bytes */, triton::uint512 concreteValue);

        //! Constructor by copy.
        MemoryAccess(const MemoryAccess& other);

        //! Destructor.
        virtual ~MemoryAccess();

        //! Initialize the address of the memory.
        void initAddress(triton::arch::CpuInterface& cpu, triton::engines::symbolic::SymbolicEngine& sEngine, bool force=false);

        //! Returns the AST of the memory access (LEA).
        triton::ast::AbstractNode* getLeaAst(void) const;

        //! Returns the address of the memory.
        triton::uint64 getAddress(void) const;

        //! Returns the highest bit of the memory vector. \sa BitsVector::getHigh()
        triton::uint32 getAbstractHigh(void) const;

        //! Returns the lower bit of the memory vector. \sa BitsVector::getLow()
        triton::uint32 getAbstractLow(void) const;

        //! Returns the size (in bits) of the memory vector.
        triton::uint32 getBitSize(void) const;

        //! Returnts the concrete value (content of the access)
        triton::uint512 getConcreteValue(void) const;

        //! LEA - Gets pc relative.
        triton::uint64 getPcRelative(void) const;

        //! Returns the size (in bytes) of the memory vector.
        triton::uint32 getSize(void) const;

        //! Returns the type of the operand (triton::arch::OP_MEM).
        triton::uint32 getType(void) const;

        //! LEA - Returns the segment register operand.
        triton::arch::Register& getSegmentRegister(void);

        //! LEA - Returns the base register operand.
        triton::arch::Register& getBaseRegister(void);

        //! LEA - Returns the index register operand.
        triton::arch::Register& getIndexRegister(void);

        //! LEA - Returns the displacement operand.
        triton::arch::Immediate& getDisplacement(void);

        //! LEA - Returns the scale operand.
        triton::arch::Immediate& getScale(void);

        //! LEA - Returns the segment register operand.
        const triton::arch::Register& getConstSegmentRegister(void) const;

        //! LEA - Returns the base register operand.
        const triton::arch::Register& getConstBaseRegister(void) const;

        //! LEA - Returns the index register operand.
        const triton::arch::Register& getConstIndexRegister(void) const;

        //! LEA - Returns the displacement operand.
        const triton::arch::Immediate& getConstDisplacement(void) const;

        //! LEA - Returns the scale operand.
        const triton::arch::Immediate& getConstScale(void) const;

        //! True if the memory is not empty.
        bool isValid(void) const;

        //! Returns true if `other` and `self` overlap.
        bool isOverlapWith(const MemoryAccess& other) const;

        //! Returns true if the memory contains a concrete value.
        bool hasConcreteValue(void) const;

        //! Sets the address of the memory access.
        void setAddress(triton::uint64 addr);

        //! Sets the concrete value of the memory access.
        void setConcreteValue(triton::uint512 concreteValue);

        //! LEA - Sets pc relative.
        void setPcRelative(triton::uint64 addr);

        //! LEA - Sets the segment register operand.
        void setSegmentRegister(triton::arch::Register& segment);

        //! LEA - Sets the base register operand.
        void setBaseRegister(triton::arch::Register& base);

        //! LEA - Sets the index register operand.
        void setIndexRegister(triton::arch::Register& index);

        //! LEA - Sets the displacement operand.
        void setDisplacement(triton::arch::Immediate& displacement);

        //! LEA - Sets the scale operand.
        void setScale(triton::arch::Immediate& scale);

        //! Copies a MemoryAccess.
        void operator=(const MemoryAccess& other);
   };

    //! Displays an MemoryAccess.
    std::ostream& operator<<(std::ostream& stream, const MemoryAccess& mem);

    //! Displays an MemoryAccess.
    std::ostream& operator<<(std::ostream& stream, const MemoryAccess* mem);

    //! Compares two MemoryAccess.
    bool operator==(const MemoryAccess& mem1, const MemoryAccess& mem2);

    //! Compares two MemoryAccess.
    bool operator!=(const MemoryAccess& mem1, const MemoryAccess& mem2);

    //! Compares two MemoryAccess (needed for std::map)
    bool operator<(const MemoryAccess& mem1, const MemoryAccess& mem2);

    //! Defines the force memory initialization constant.
    const bool FORCE_MEMORY_INITIALIZATION = true;

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_MEMORYACCESS */
