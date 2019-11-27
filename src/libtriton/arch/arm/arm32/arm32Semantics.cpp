//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <utility>
#include <triton/arm32Semantics.hpp>
#include <triton/arm32Specifications.hpp>
#include <triton/astContext.hpp>
#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>



namespace triton {
  namespace arch {
    namespace arm32 {

      Arm32Semantics::Arm32Semantics(triton::arch::Architecture* architecture,
                                     triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                                     triton::engines::taint::TaintEngine* taintEngine,
                                     const triton::ast::SharedAstContext& astCtxt) {

        this->architecture    = architecture;
        this->astCtxt         = astCtxt;
        this->symbolicEngine  = symbolicEngine;
        this->taintEngine     = taintEngine;

        if (architecture == nullptr)
          throw triton::exceptions::Semantics("Arm32Semantics::Arm32Semantics(): The architecture API must be defined.");

        if (this->symbolicEngine == nullptr)
          throw triton::exceptions::Semantics("Arm32Semantics::Arm32Semantics(): The symbolic engine API must be defined.");

        if (this->taintEngine == nullptr)
          throw triton::exceptions::Semantics("Arm32Semantics::Arm32Semantics(): The taint engines API must be defined.");
      }


      bool Arm32Semantics::buildSemantics(triton::arch::Instruction& inst) {
        return true;
      }


    }; /* arm32 namespace */
  }; /* arch namespace */
}; /* triton namespace */
