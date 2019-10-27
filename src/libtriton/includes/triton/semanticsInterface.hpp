//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SEMANTICSINTERFACE_HPP
#define TRITON_SEMANTICSINTERFACE_HPP

#include <triton/triton_export.h>
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

        //! Builds the semantics of the instruction. Returns true if the instruction is supported.
        TRITON_EXPORT virtual bool buildSemantics(triton::arch::Instruction& inst) = 0;
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SEMANTICSINTERFACE_HPP */
