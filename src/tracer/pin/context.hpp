//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_PIN_CONTEXT_H
#define TRITON_PIN_CONTEXT_H

#include <pin.H>

/* libTriton */
#include <api.hpp>
#include <tritonTypes.hpp>



//! \module The Tracer namespace
namespace tracer {
/*!
 *  \addtogroup tracer
 *  @{
 */

  //! \module The pintool namespace
  namespace pintool {
  /*!
   *  \ingroup tracer
   *  \addtogroup pintool
   *  @{
   */

    //! \module The context namespace
    namespace context {
    /*!
     *  \ingroup pintool
     *  \addtogroup context
     *  @{
     */

      //! The last Pin CONTEXT known.
      extern CONTEXT* lastContext;

      //! True if the context must be executed.
      extern bool mustBeExecuted;

      //! Returns the current register value from a RegisterOperand.
      triton::uint128 getCurrentRegisterValue(triton::arch::RegisterOperand& reg);

      //! Returns the current memory value from a MemoryOperand.
      triton::uint128 getCurrentMemoryValue(triton::arch::MemoryOperand& mem);

      //! Returns the current memory value from an address.
      triton::uint128 getCurrentMemoryValue(triton::__uint addr);

      //! Returns the current memory value from an address with a specified readable size.
      triton::uint128 getCurrentMemoryValue(triton::__uint addr, triton::uint32 size);

      //! Sets the current register value from a RegisterOperand. `triton::arch::RegisterOperand::getConcreteValue()` is used to define the value.
      void setCurrentRegisterValue(triton::arch::RegisterOperand& reg);

      //! Sets the current register value from a RegisterOperand.
      void setCurrentRegisterValue(triton::arch::RegisterOperand& reg, triton::uint128 value);

      //! Sets the current memory value from a MemoryOperand. `triton::arch::MemoryOperand::getConcreteValue()` is used to define the value.
      void setCurrentMemoryValue(triton::arch::MemoryOperand& mem);

      //! Sets the current memory value from a MemoryOperand.
      void setCurrentMemoryValue(triton::arch::MemoryOperand& mem, triton::uint128 value);

      //! Sets the current memory value from an address.
      void setCurrentMemoryValue(triton::__uint addr, triton::uint8 value);

      //! Executes the new context.
      void executeContext(void);

      //! Setups the context register from Pin to Triton.
      void setupContextRegister(triton::arch::Instruction* inst, CONTEXT* ctx);

    /*! @} End of context namespace */
    };
  /*! @} End of pintool namespace */
  };
/*! @} End of tracer namespace */
};

#endif // TRITON_PIN_TRIGGER_H
