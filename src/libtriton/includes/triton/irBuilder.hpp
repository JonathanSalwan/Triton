//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_IRBUILDER_H
#define TRITON_IRBUILDER_H

#include <triton/architecture.hpp>
#include <triton/astGarbageCollector.hpp>
#include <triton/instruction.hpp>
#include <triton/modes.hpp>
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

    /*! \class IrBuilder
     *  \brief The IR builder. */
    class IrBuilder {
      private:
        //! Architecture API
        triton::arch::Architecture* architecture;

        //! AST garbage collector API
        triton::ast::AstGarbageCollector* astGarbageCollector;

        //! Backup AST garbage collector
        triton::ast::AstGarbageCollector* backupAstGarbageCollector;

        //! Modes API
        triton::modes::Modes* modes;

        //! Symbolic engine API
        triton::engines::symbolic::SymbolicEngine* symbolicEngine;

        //! Backup symbolic engine
        triton::engines::symbolic::SymbolicEngine* backupSymbolicEngine;

        //! Taint engine API
        triton::engines::taint::TaintEngine* taintEngine;

        //! Removes all symbolic expressions of an instruction.
        void removeSymbolicExpressions(triton::arch::Instruction& inst, std::set<triton::ast::AbstractNode*>& uniqueNodes);

      protected:
        //! x86 ISA builder.
        triton::arch::SemanticsInterface* x86Isa;

      public:
        //! Constructor.
        IrBuilder(triton::arch::Architecture* architecture,
                  triton::modes::Modes* modes,
                  triton::ast::AstGarbageCollector* astGarbageCollector,
                  triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                  triton::engines::taint::TaintEngine* taintEngine);

        //! Destructor.
        virtual ~IrBuilder();

        //! Builds the semantics of the instruction. Returns true if the instruction is supported.
        bool buildSemantics(triton::arch::Instruction& inst);

        //! Everything which must be done before buiding the semantics
        void preIrInit(triton::arch::Instruction& inst);

        //! Everything which must be done after building the semantics.
        void postIrInit(triton::arch::Instruction& inst);
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_IRBUILDER_H */
