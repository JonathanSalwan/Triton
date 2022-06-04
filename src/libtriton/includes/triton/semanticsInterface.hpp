//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_SEMANTICSINTERFACE_HPP
#define TRITON_SEMANTICSINTERFACE_HPP

#include <triton/archEnums.hpp>
#include <triton/dllexport.hpp>
#include <triton/instruction.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Architecture namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    /*! \interface SemanticsInterface
        \brief This interface is used as abstract semantics interface. All ISA semantics must use this interface. */
    class SemanticsInterface {
      public:
        //! Destructor.
        TRITON_EXPORT virtual ~SemanticsInterface(){};

        //! Builds the semantics of the instruction. Returns `triton::arch::NO_FAULT` if succeed.
        TRITON_EXPORT virtual triton::arch::exception_e buildSemantics(triton::arch::Instruction& inst) = 0;
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SEMANTICSINTERFACE_HPP */
