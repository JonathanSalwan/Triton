//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_OPERANDWRAPPER_HPP
#define TRITON_OPERANDWRAPPER_HPP

#include <triton/archEnums.hpp>
#include <triton/triton_export.h>
#include <triton/immediate.hpp>
#include <triton/memoryAccess.hpp>
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

    /*! \interface OperandWrapper
     *  \brief This class is used as operand wrapper.
     */
    class OperandWrapper {
      private:
        //! If the operand is an immediate, this attribute is filled.
        triton::arch::Immediate imm;

        //! If the operand is a memory, this attribute is filled.
        triton::arch::MemoryAccess mem;

        //! If the operand is a register, this attribute is filled.
        triton::arch::Register reg;

        //! The type of the operand.
        triton::arch::operand_e type;

      public:
        //! Immediate constructor.
        TRITON_EXPORT OperandWrapper(const triton::arch::Immediate& imm);

        //! Memory constructor.
        TRITON_EXPORT OperandWrapper(const triton::arch::MemoryAccess& mem);

        //! Register constructor.
        TRITON_EXPORT OperandWrapper(const triton::arch::Register& reg);

        //! Constructor by copy.
        TRITON_EXPORT OperandWrapper(const OperandWrapper& other);

        //! Returns the abstract type of the operand.
        TRITON_EXPORT triton::arch::operand_e getType(void) const;

        //! Returns the immediate operand.
        TRITON_EXPORT triton::arch::Immediate& getImmediate(void);

        //! Returns the memory operand.
        TRITON_EXPORT triton::arch::MemoryAccess& getMemory(void);

        //! Returns the register operand.
        TRITON_EXPORT triton::arch::Register& getRegister(void);

        //! Returns the immediate operand.
        TRITON_EXPORT const triton::arch::Immediate& getConstImmediate(void) const;

        //! Returns the memory operand as const.
        TRITON_EXPORT const triton::arch::MemoryAccess& getConstMemory(void) const;

        //! Returns the register operand.
        TRITON_EXPORT const triton::arch::Register& getConstRegister(void) const;

        //! Sets the immediate operand.
        TRITON_EXPORT void setImmediate(const triton::arch::Immediate& imm);

        //! Sets the memory operand.
        TRITON_EXPORT void setMemory(const triton::arch::MemoryAccess& mem);

        //! Sets the register operand.
        TRITON_EXPORT void setRegister(const triton::arch::Register& reg);

        //! Returns the abstract size (in bytes) of the operand.
        TRITON_EXPORT triton::uint32 getSize(void) const;

        //! Returns the abstract size (in bits) of the operand.
        TRITON_EXPORT triton::uint32 getBitSize(void) const;

        //! Returns the highest bit position of the abstract operand.
        TRITON_EXPORT triton::uint32 getHigh(void) const;

        //! Returns the lower bit position of the abstract operand.
        TRITON_EXPORT triton::uint32 getLow(void) const;

        //! Copies a OperandWrapper.
        TRITON_EXPORT OperandWrapper& operator=(const OperandWrapper& other);

        //! Tests two OperandWrappers for equality.
        TRITON_EXPORT bool operator==(const OperandWrapper& other) const;

        //! Tests two OperandWrappers for not equality.
        TRITON_EXPORT bool operator!=(const OperandWrapper& other) const;

        //! Compares two OperandWrappers for ordering.
        TRITON_EXPORT bool operator<(const OperandWrapper& other) const;
    };

    //! Displays a OperandWrapper according to the concrete type.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const triton::arch::OperandWrapper& op);

    //! Displays a OperandWrapper according to the concrete type.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const triton::arch::OperandWrapper* op);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_OPERANDWRAPPER_HPP */
