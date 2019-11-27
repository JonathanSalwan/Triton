//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ARM32SEMANTICS_H
#define TRITON_ARM32SEMANTICS_H

#include <triton/architecture.hpp>
#include <triton/dllexport.hpp>
#include <triton/instruction.hpp>
#include <triton/semanticsInterface.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/taintEngine.hpp>



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

    //! The arm32 namespace
    namespace arm32 {
    /*!
     *  \ingroup arch
     *  \addtogroup arm32
     *  @{
     */

      /*! \class Arm32Semantics
          \brief The Arm32 ISA semantics. */
      class Arm32Semantics : public SemanticsInterface {
        private:
          //! Architecture API
          triton::arch::Architecture* architecture;

          //! Symbolic Engine API
          triton::engines::symbolic::SymbolicEngine* symbolicEngine;

          //! Taint Engine API
          triton::engines::taint::TaintEngine* taintEngine;

          //! The AST Context API
          triton::ast::SharedAstContext astCtxt;

        public:
          //! Constructor.
          TRITON_EXPORT Arm32Semantics(triton::arch::Architecture* architecture,
                                       triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                                       triton::engines::taint::TaintEngine* taintEngine,
                                       const triton::ast::SharedAstContext& astCtxt);

          //! Builds the semantics of the instruction. Returns true if the instruction is supported.
          TRITON_EXPORT bool buildSemantics(triton::arch::Instruction& inst);

      };

    /*! @} End of arm32 namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ARM32SEMANTICS_H */
