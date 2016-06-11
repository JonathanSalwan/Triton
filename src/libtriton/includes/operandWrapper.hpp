//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_OPERANDWRAPPER_H
#define TRITON_OPERANDWRAPPER_H

#include "immediateOperand.hpp"
#include "memoryOperand.hpp"
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

    /*! \interface OperandWrapper
     *  \brief This class is used as operand wrapper.
     */
    class OperandWrapper {
      public:
        //! If the operand is an immediate, this attribute is filled.
        ImmediateOperand imm;

        //! If the operand is an immediate, this attribute is filled.
        MemoryOperand mem;

        //! If the operand is an immediate, this attribute is filled.
        RegisterOperand reg;

        //! The type of the operand.
        triton::uint32 type;

        //! Immediate constructor.
        OperandWrapper(const ImmediateOperand& imm);

        //! Memory constructor.
        OperandWrapper(const MemoryOperand& mem);

        //! Register constructor.
        OperandWrapper(const RegisterOperand& reg);

        //! Destructor.
        ~OperandWrapper();

        //! Returns the abstract type of the operand.
        triton::uint32 getType(void) const;

        //! Returns the immediate operand.
        ImmediateOperand& getImmediate(void);

        //! Returns the memroy operand.
        MemoryOperand& getMemory(void);

        //! Returns the register operand.
        RegisterOperand& getRegister(void);

        //! Returns the immediate operand.
        const ImmediateOperand& getConstImmediate(void) const;

        //! Returns the memroy operand.
        const MemoryOperand& getConstMemory(void) const;

        //! Returns the register operand.
        const RegisterOperand& getConstRegister(void) const;

        //! Sets the immediate operand.
        void setImmediate(const ImmediateOperand& imm);

        //! Sets the memroy operand.
        void setMemory(const MemoryOperand& mem);

        //! Sets the register operand.
        void setRegister(const RegisterOperand& reg);

        //! True if this concrete abstract value is trusted and synchronized with the real CPU/MMU value.
        bool isTrusted(void) const;

        //! Sets the trust flag.
        void setTrust(bool flag);

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

