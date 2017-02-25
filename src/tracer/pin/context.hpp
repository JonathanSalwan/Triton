//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PIN_CONTEXT_H
#define TRITON_PIN_CONTEXT_H

#include <pin.H>

/* libTriton */
#include <triton/api.hpp>
#include <triton/tritonTypes.hpp>



//! The Tracer namespace
namespace tracer {
/*!
 *  \addtogroup tracer
 *  @{
 */

  //! The Pintool namespace
  namespace pintool {
  /*!
   *  \ingroup tracer
   *  \addtogroup pintool
   *  @{
   */

    //! The Context namespace
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

      //! Returns the current register value from a Register.
      triton::uint512 getCurrentRegisterValue(const triton::arch::Register& reg);

      //! Returns the current memory value from a MemoryAccess.
      triton::uint512 getCurrentMemoryValue(const triton::arch::MemoryAccess& mem);

      //! Returns the current memory value from an address.
      triton::uint512 getCurrentMemoryValue(triton::__uint addr);

      //! Returns the current memory value from an address with a specified readable size.
      triton::uint512 getCurrentMemoryValue(triton::__uint addr, triton::uint32 size);

      //! Sets the current register value from a Register. `triton::arch::Register::getConcreteValue()` is used to define the value.
      void setCurrentRegisterValue(triton::arch::Register& reg);

      //! Sets the current register value from a Register.
      void setCurrentRegisterValue(triton::arch::Register& reg, triton::uint512 value);

      //! Sets the current memory value from a MemoryAccess. `triton::arch::MemoryAccess::getConcreteValue()` is used to define the value.
      void setCurrentMemoryValue(triton::arch::MemoryAccess& mem);

      //! Sets the current memory value from a MemoryAccess.
      void setCurrentMemoryValue(triton::arch::MemoryAccess& mem, triton::uint512 value);

      //! Sets the current memory value from an address.
      void setCurrentMemoryValue(triton::__uint addr, triton::uint8 value);

      //! Executes the new context.
      void executeContext(void);

      //! Callback to provide concrete register values only if Triton needs them - cf #376
      void needConcreteRegisterValue(triton::arch::Register& reg);

      //! Synchronize weird behavior from Pin to libTriton.
      void synchronizeContext(void);

    /*! @} End of context namespace */
    };
  /*! @} End of pintool namespace */
  };
/*! @} End of tracer namespace */
};

#endif // TRITON_PIN_TRIGGER_H
