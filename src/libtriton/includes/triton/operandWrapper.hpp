//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_OPERANDWRAPPER_H
#define TRITON_OPERANDWRAPPER_H

#include <triton/immediate.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/operandInterface.hpp>
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
      public:
        //! If the operand is an immediate, this attribute is filled.
        triton::arch::Immediate imm;

        //! If the operand is a memory, this attribute is filled.
        triton::arch::MemoryAccess mem;

        //! If the operand is a register, this attribute is filled.
        triton::arch::Register reg;

        //! The type of the operand.
        triton::uint32 type;

        //! Immediate constructor.
        OperandWrapper(const triton::arch::Immediate& imm);

        //! Memory constructor.
        OperandWrapper(const triton::arch::MemoryAccess& mem);

        //! Register constructor.
        OperandWrapper(const triton::arch::Register& reg);

        //! Destructor.
        virtual ~OperandWrapper();

        //! Returns the abstract type of the operand.
        triton::uint32 getType(void) const;

        //! Returns the immediate operand.
        triton::arch::Immediate& getImmediate(void);

        //! Returns the memory operand.
        triton::arch::MemoryAccess& getMemory(void);

        //! Returns the register operand.
        triton::arch::Register& getRegister(void);

        //! Returns the immediate operand.
        const triton::arch::Immediate& getConstImmediate(void) const;

        //! Returns the memory operand as const.
        const triton::arch::MemoryAccess& getConstMemory(void) const;

        //! Returns the register operand.
        const triton::arch::Register& getConstRegister(void) const;

        //! Sets the immediate operand.
        void setImmediate(const triton::arch::Immediate& imm);

        //! Sets the memory operand.
        void setMemory(const triton::arch::MemoryAccess& mem);

        //! Sets the register operand.
        void setRegister(const triton::arch::Register& reg);

        //! Returns the abstract size (in bytes) of the operand.
        triton::uint32 getSize(void) const;

        //! Returns the abstract size (in bits) of the operand.
        triton::uint32 getBitSize(void) const;

        //! Returns the highest bit position of the abstract operand.
        triton::uint32 getAbstractHigh(void) const;

        //! Returns the lower bit position of the abstract operand.
        triton::uint32 getAbstractLow(void) const;

        //! Returns the abstract concrete value.
        triton::uint512 getConcreteValue(void) const;

        //! Copies a OperandWrapper.
        void operator=(const OperandWrapper& other);

        //! Tests two OperandWrappers for equality.
        bool operator==(const OperandWrapper& other) const;

        //! Compares two OperandWrappers for ordering.
        bool operator<(const OperandWrapper& other) const;
    };

    //! Displays a OperandWrapper according to the concrete type.
    std::ostream& operator<<(std::ostream& stream, const triton::arch::OperandWrapper& op);

    //! Displays a OperandWrapper according to the concrete type.
    std::ostream& operator<<(std::ostream& stream, const triton::arch::OperandWrapper* op);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_OPERANDWRAPPER_H */

