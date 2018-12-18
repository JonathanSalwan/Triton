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

          //! Creates a conditional node.
          triton::ast::SharedAbstractNode getCodeConditionAst(triton::arch::Instruction& inst,
                                                              triton::ast::SharedAbstractNode& thenNode,
                                                              triton::ast::SharedAbstractNode& elseNode);

          //! Gets the taint state (based on flags) of a conditional instruction
          bool getCodeConditionTainteSate(const triton::arch::Instruction& inst);

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

          //! The B and B.cond semantics.
          void b_s(triton::arch::Instruction& inst);

          //! The BL semantics.
          void bl_s(triton::arch::Instruction& inst);

          //! The BLR semantics.
          void blr_s(triton::arch::Instruction& inst);

          //! The BR semantics.
          void br_s(triton::arch::Instruction& inst);

          //! The CBNZ semantics
          void cbnz_s(triton::arch::Instruction& inst);

          //! The CBZ semantics
          void cbz_s(triton::arch::Instruction& inst);

          //! The EON semantics.
          void eon_s(triton::arch::Instruction& inst);

          //! The EOR semantics.
          void eor_s(triton::arch::Instruction& inst);

          //! The EXTR semantics.
          void extr_s(triton::arch::Instruction& inst);

          //! The LDR semantics.
          void ldr_s(triton::arch::Instruction& inst);

          //! The LDUR semantics.
          void ldur_s(triton::arch::Instruction& inst);

          //! The LDURB semantics.
          void ldurb_s(triton::arch::Instruction& inst);

          //! The LDURH semantics.
          void ldurh_s(triton::arch::Instruction& inst);

          //! The LDURSB semantics.
          void ldursb_s(triton::arch::Instruction& inst);

          //! The LDURSH semantics.
          void ldursh_s(triton::arch::Instruction& inst);

          //! The LDURSW semantics.
          void ldursw_s(triton::arch::Instruction& inst);

          //! The MADD semantics.
          void madd_s(triton::arch::Instruction& inst);

          //! The MOV semantics.
          void mov_s(triton::arch::Instruction& inst);

          //! The MOVZ semantics.
          void movz_s(triton::arch::Instruction& inst);

          //! The MSUB semantics.
          void msub_s(triton::arch::Instruction& inst);

          //! The MVN semantics.
          void mvn_s(triton::arch::Instruction& inst);

          //! The NEG semantics.
          void neg_s(triton::arch::Instruction& inst);

          //! The NOP semantics.
          void nop_s(triton::arch::Instruction& inst);

          //! The ORN semantics.
          void orn_s(triton::arch::Instruction& inst);

          //! The RET semantics.
          void ret_s(triton::arch::Instruction& inst);

          //! The STR semantics.
          void str_s(triton::arch::Instruction& inst);

          //! The STUR semantics.
          void stur_s(triton::arch::Instruction& inst);

          //! The STURB semantics.
          void sturb_s(triton::arch::Instruction& inst);

          //! The STURH semantics.
          void sturh_s(triton::arch::Instruction& inst);

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
