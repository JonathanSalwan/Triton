//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_IRBUILDER_H
#define TRITON_IRBUILDER_H

#include <triton/archEnums.hpp>
#include <triton/architecture.hpp>
#include <triton/basicBlock.hpp>
#include <triton/dllexport.hpp>
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

        //! Modes API
        triton::modes::SharedModes modes;

        //! AstContext API
        triton::ast::SharedAstContext astCtxt;

        //! Symbolic engine API
        triton::engines::symbolic::SymbolicEngine* symbolicEngine;

        //! Taint engine API
        triton::engines::taint::TaintEngine* taintEngine;

        //! Removes all symbolic expressions of an instruction.
        void removeSymbolicExpressions(triton::arch::Instruction& inst);

        //! Collects nodes from a set.
        template <typename T> void collectNodes(T& items) const;

        //! Collects nodes from operands.
        void collectNodes(std::vector<triton::arch::OperandWrapper>& operands) const;

        //! Collects unsymbolized nodes from a set.
        template <typename T> void collectUnsymbolizedNodes(T& items) const;

        //! Collects unsymbolized nodes from operands.
        void collectUnsymbolizedNodes(std::vector<triton::arch::OperandWrapper>& operands) const;

      protected:
        //! AArch64 ISA builder.
        triton::arch::SemanticsInterface* aarch64Isa;

        //! ARM32 ISA builder.
        triton::arch::SemanticsInterface* arm32Isa;

        //! x86 ISA builder.
        triton::arch::SemanticsInterface* x86Isa;

      public:
        //! Constructor.
        TRITON_EXPORT IrBuilder(triton::arch::Architecture* architecture,
                                const triton::modes::SharedModes& modes,
                                const triton::ast::SharedAstContext& astCtxt,
                                triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                                triton::engines::taint::TaintEngine* taintEngine);

        //! Destructor.
        TRITON_EXPORT virtual ~IrBuilder();

        //! Builds the semantics of the instruction. Returns `triton::arch::NO_FAULT` if succeed.
        TRITON_EXPORT triton::arch::exception_e buildSemantics(triton::arch::Instruction& inst);

        //! Builds the semantics of instructions in a block. Returns `triton::arch::NO_FAULT` if succeed.
        TRITON_EXPORT triton::arch::exception_e buildSemantics(triton::arch::BasicBlock& block);

        //! Everything which must be done before buiding the semantics
        TRITON_EXPORT void preIrInit(triton::arch::Instruction& inst);

        //! Everything which must be done after building the semantics.
        TRITON_EXPORT void postIrInit(triton::arch::Instruction& inst);
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_IRBUILDER_H */
