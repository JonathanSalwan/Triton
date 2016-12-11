//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_IRBUILDER_H
#define TRITON_IRBUILDER_H

#include "architecture.hpp"
#include "instruction.hpp"
#include "semanticsInterface.hpp"
#include "symbolicEngine.hpp"
#include "taintEngine.hpp"



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

    /*! \class IrBuilder
     *  \brief The IR builder. */
    class IrBuilder {
      private:
        //! Architecture API
        triton::arch::Architecture* architecture;

        //! Symbolic Engine API
        triton::engines::symbolic::SymbolicEngine* symbolicEngine;

        //! Taint Engine API
        triton::engines::taint::TaintEngine* taintEngine;

      protected:
        //! x86 ISA builder.
        triton::arch::SemanticsInterface* x86Isa;

      public:
        //! Constructor.
        IrBuilder(triton::arch::Architecture* architecture,
                  triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                  triton::engines::taint::TaintEngine* taintEngine);

        //! Destructor.
        virtual ~IrBuilder();

        //! Builds the semantics of the instruction. Returns true if the instruction is supported.
        bool buildSemantics(triton::arch::Instruction& inst);
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_IRBUILDER_H */
