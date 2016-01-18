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

        //! If the operand's type.
        triton::uint32 type;

        //! Immediate constructor.
        OperandWrapper(ImmediateOperand imm);

        //! Memory constructor.
        OperandWrapper(MemoryOperand mem);

        //! Register constructor.
        OperandWrapper(RegisterOperand reg);

        //! Destructor.
        ~OperandWrapper();

        //! Returns the abstract operand's type.
        triton::uint32 getType(void) const;

        //! Returns the immediate operand.
        ImmediateOperand& getImm(void);

        //! Returns the memroy operand.
        MemoryOperand& getMem(void);

        //! Returns the register operand.
        RegisterOperand& getReg(void);

        //! Sets the immediate operand.
        void setImm(ImmediateOperand imm);

        //! Sets the memroy operand.
        void setMem(MemoryOperand mem);

        //! Sets the register operand.
        void setReg(RegisterOperand reg);

        //! True if this concrete abstract value is trusted and synchronized with the real CPU/MMU value.
        bool isTrusted(void);

        //! Sets the trust flag.
        void setTrust(bool flag);

        //! Returns the abstract operand's size (in bytes).
        triton::uint32 getSize(void);

        //! Returns the abstract operand's size (in bits).
        triton::uint32 getBitSize(void);

        //! Returns the highest bit position of the abstract operand.
        triton::uint32 getAbstractHigh(void);

        //! Returns the lower bit position of the abstract operand.
        triton::uint32 getAbstractLow(void);

        //! Returns the abstract concrete value.
        triton::uint128 getConcreteValue(void);
    };

    //! Displays a OperandWrapper according to the concrete type.
    std::ostream &operator<<(std::ostream &stream, triton::arch::OperandWrapper op);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_OPERANDWRAPPER_H */

