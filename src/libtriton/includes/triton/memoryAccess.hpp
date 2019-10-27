//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_MEMORYACCESS_HPP
#define TRITON_MEMORYACCESS_HPP

#include <triton/aarch64OperandProperties.hpp>
#include <triton/archEnums.hpp>
#include <triton/ast.hpp>
#include <triton/bitsVector.hpp>
#include <triton/cpuSize.hpp>
#include <triton/triton_export.h>
#include <triton/immediate.hpp>
#include <triton/register.hpp>
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

    /*! \class MemoryAccess
     *  \brief This class is used to represent a memory access.
     */
    class MemoryAccess : public BitsVector {
      protected:
        //! The memory' address.
        triton::uint64 address;

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

        //! The AST of the memory access (LEA).
        triton::ast::SharedAbstractNode leaAst;

      private:
        //! Copy a MemoryAccess.
        void copy(const MemoryAccess& other);

      public:
        //! Constructor.
        TRITON_EXPORT MemoryAccess();

        //! Constructor.
        TRITON_EXPORT MemoryAccess(triton::uint64 address, triton::uint32 size /* bytes */);

        //! Constructor by copy.
        TRITON_EXPORT MemoryAccess(const MemoryAccess& other);

        //! Returns the AST of the memory access (LEA).
        TRITON_EXPORT triton::ast::SharedAbstractNode getLeaAst(void) const;

        //! Returns the address of the memory.
        TRITON_EXPORT triton::uint64 getAddress(void) const;

        //! LEA - Gets pc relative.
        TRITON_EXPORT triton::uint64 getPcRelative(void) const;

        //! Returns the size (in bits) of the memory vector.
        TRITON_EXPORT triton::uint32 getBitSize(void) const;

        //! Returns the size (in bytes) of the memory vector.
        TRITON_EXPORT triton::uint32 getSize(void) const;

        //! Returns the type of the operand (triton::arch::OPERAND_MEMORY).
        TRITON_EXPORT triton::arch::operand_e getType(void) const;

        //! LEA - Returns the segment register operand.
        TRITON_EXPORT triton::arch::Register& getSegmentRegister(void);

        //! LEA - Returns the base register operand.
        TRITON_EXPORT triton::arch::Register& getBaseRegister(void);

        //! LEA - Returns the index register operand.
        TRITON_EXPORT triton::arch::Register& getIndexRegister(void);

        //! LEA - Returns the displacement operand.
        TRITON_EXPORT triton::arch::Immediate& getDisplacement(void);

        //! LEA - Returns the scale operand.
        TRITON_EXPORT triton::arch::Immediate& getScale(void);

        //! LEA - Returns the segment register operand.
        TRITON_EXPORT const triton::arch::Register& getConstSegmentRegister(void) const;

        //! LEA - Returns the base register operand.
        TRITON_EXPORT const triton::arch::Register& getConstBaseRegister(void) const;

        //! LEA - Returns the index register operand.
        TRITON_EXPORT const triton::arch::Register& getConstIndexRegister(void) const;

        //! LEA - Returns the displacement operand.
        TRITON_EXPORT const triton::arch::Immediate& getConstDisplacement(void) const;

        //! LEA - Returns the scale operand.
        TRITON_EXPORT const triton::arch::Immediate& getConstScale(void) const;

        //! Returns true if `other` and `self` overlap.
        TRITON_EXPORT bool isOverlapWith(const MemoryAccess& other) const;

        //! Sets the address of the memory access.
        TRITON_EXPORT void setAddress(triton::uint64 addr);

        //! LEA - Sets pc relative.
        TRITON_EXPORT void setPcRelative(triton::uint64 addr);

        //! LEA - Sets the segment register operand.
        TRITON_EXPORT void setSegmentRegister(const triton::arch::Register& segment);

        //! LEA - Sets the base register operand.
        TRITON_EXPORT void setBaseRegister(const triton::arch::Register& base);

        //! LEA - Sets the index register operand.
        TRITON_EXPORT void setIndexRegister(const triton::arch::Register& index);

        //! LEA - Sets the displacement operand.
        TRITON_EXPORT void setDisplacement(const triton::arch::Immediate& displacement);

        //! LEA - Sets the scale operand.
        TRITON_EXPORT void setScale(const triton::arch::Immediate& scale);

        //! Sets the AST of the memory access (LEA).
        TRITON_EXPORT void setLeaAst(const triton::ast::SharedAbstractNode& ast);

        //! Copies a MemoryAccess.
        TRITON_EXPORT MemoryAccess& operator=(const MemoryAccess& other);
    };

    //! Displays an MemoryAccess.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const MemoryAccess& mem);

    //! Displays an MemoryAccess.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const MemoryAccess* mem);

    //! Compares two MemoryAccess.
    TRITON_EXPORT bool operator==(const MemoryAccess& mem1, const MemoryAccess& mem2);

    //! Compares two MemoryAccess.
    TRITON_EXPORT bool operator!=(const MemoryAccess& mem1, const MemoryAccess& mem2);

    //! Compares two MemoryAccess (needed for std::map)
    TRITON_EXPORT bool operator<(const MemoryAccess& mem1, const MemoryAccess& mem2);

    //! Defines the force memory initialization constant.
    const bool FORCE_MEMORY_INITIALIZATION = true;

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_MEMORYACCESS_HPP */
