//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_AARCH64SEMANTICS_H
#define TRITON_AARCH64SEMANTICS_H

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

    //! The aarch64 namespace
    namespace aarch64 {
    /*!
     *  \ingroup arch
     *  \addtogroup aarch64
     *  @{
     */

      /*! \class AArch64Semantics
          \brief The AArch64 ISA semantics. */
      class AArch64Semantics : public SemanticsInterface {
        private:
          //! Architecture API
          triton::arch::Architecture* architecture;

          //! Symbolic Engine API
          triton::engines::symbolic::SymbolicEngine* symbolicEngine;

          //! Taint Engine API
          triton::engines::taint::TaintEngine* taintEngine;

          triton::ast::AstContext& astCtxt;

        public:
          //! Constructor.
          TRITON_EXPORT AArch64Semantics(triton::arch::Architecture* architecture,
                                         triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                                         triton::engines::taint::TaintEngine* taintEngine,
                                         triton::ast::AstContext& astCtxt);

          //! Builds the semantics of the instruction. Returns true if the instruction is supported.
          TRITON_EXPORT bool buildSemantics(triton::arch::Instruction& inst);

        private:
          //! Control flow semantics. Used to represent PC.
          void controlFlow_s(triton::arch::Instruction& inst);

          //! The ADC semantics.
          void adc_s(triton::arch::Instruction& inst);

          //! The ADD semantics.
          void add_s(triton::arch::Instruction& inst);

          //! The ADR semantics.
          void adr_s(triton::arch::Instruction& inst);

          //! The ADRP semantics.
          void adrp_s(triton::arch::Instruction& inst);

          //! The AND semantics.
          void and_s(triton::arch::Instruction& inst);

          //! The ASR semantics.
          void asr_s(triton::arch::Instruction& inst);

          //! The EON semantics.
          void eon_s(triton::arch::Instruction& inst);

          //! The EOR semantics.
          void eor_s(triton::arch::Instruction& inst);

          //! The LDR semantics.
          void ldr_s(triton::arch::Instruction& inst);

          //! The MOVZ semantics.
          void movz_s(triton::arch::Instruction& inst);

          //! The ORN semantics.
          void orn_s(triton::arch::Instruction& inst);

          //! The SUB semantics.
          void sub_s(triton::arch::Instruction& inst);
      };

    /*! @} End of aarch64 namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_AARCH64SEMANTICS_H */
