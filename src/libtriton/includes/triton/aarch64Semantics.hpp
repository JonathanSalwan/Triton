//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_AARCH64SEMANTICS_H
#define TRITON_AARCH64SEMANTICS_H

#include <triton/architecture.hpp>
#include <triton/triton_export.h>
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

          //! The AST Context API
          triton::ast::SharedAstContext astCtxt;

        public:
          //! Constructor.
          TRITON_EXPORT AArch64Semantics(triton::arch::Architecture* architecture,
                                         triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                                         triton::engines::taint::TaintEngine* taintEngine,
                                         const triton::ast::SharedAstContext& astCtxt);

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

          /* Generic flags computation ------------------------------------- */

          //! Clears a flag.
          void clearFlag_s(triton::arch::Instruction& inst, const triton::arch::Register& flag, std::string comment="");

          //! Sets a flag.
          void setFlag_s(triton::arch::Instruction& inst, const triton::arch::Register& flag, std::string comment="");

          //! The NF semantics.
          void nf_s(triton::arch::Instruction& inst,
                    const triton::engines::symbolic::SharedSymbolicExpression& parent,
                    triton::arch::OperandWrapper& dst);

          //! The NF semantics for the CCMP operation.
          void nfCcmp_s(triton::arch::Instruction& inst,
                        const triton::engines::symbolic::SharedSymbolicExpression& parent,
                        triton::arch::OperandWrapper& dst,
                        triton::ast::SharedAbstractNode& nzcv);

          //! The ZF semantics.
          void zf_s(triton::arch::Instruction& inst,
                    const triton::engines::symbolic::SharedSymbolicExpression& parent,
                    triton::arch::OperandWrapper& dst);

          //! The ZF semantics for the CCMP operation.
          void zfCcmp_s(triton::arch::Instruction& inst,
                        const triton::engines::symbolic::SharedSymbolicExpression& parent,
                        triton::arch::OperandWrapper& dst,
                        triton::ast::SharedAbstractNode& nzcv);

          /* Specific flags computation ------------------------------------ */

          //! The CF semantics for the ADDS operation.
          void cfAdd_s(triton::arch::Instruction& inst,
                       const triton::engines::symbolic::SharedSymbolicExpression& parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::SharedAbstractNode& op1,
                       triton::ast::SharedAbstractNode& op2);

          //! The CF semantics for the SUBS operation.
          void cfSub_s(triton::arch::Instruction& inst,
                       const triton::engines::symbolic::SharedSymbolicExpression& parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::SharedAbstractNode& op1,
                       triton::ast::SharedAbstractNode& op2);

          //! The CF semantics for the CCMP operation.
          void cfCcmp_s(triton::arch::Instruction& inst,
                        const triton::engines::symbolic::SharedSymbolicExpression& parent,
                        triton::arch::OperandWrapper& dst,
                        triton::ast::SharedAbstractNode& op1,
                        triton::ast::SharedAbstractNode& op2,
                        triton::ast::SharedAbstractNode& nzcv);

          //! The VF semantics for the ADDS operation.
          void vfAdd_s(triton::arch::Instruction& inst,
                       const triton::engines::symbolic::SharedSymbolicExpression& parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::SharedAbstractNode& op1,
                       triton::ast::SharedAbstractNode& op2);

          //! The VF semantics for the SUBS operation.
          void vfSub_s(triton::arch::Instruction& inst,
                       const triton::engines::symbolic::SharedSymbolicExpression& parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::SharedAbstractNode& op1,
                       triton::ast::SharedAbstractNode& op2);

          //! The VF semantics for the CCMP operation.
          void vfCcmp_s(triton::arch::Instruction& inst,
                        const triton::engines::symbolic::SharedSymbolicExpression& parent,
                        triton::arch::OperandWrapper& dst,
                        triton::ast::SharedAbstractNode& op1,
                        triton::ast::SharedAbstractNode& op2,
                        triton::ast::SharedAbstractNode& nzcv);

          /* Instruction semantics ----------------------------------------- */

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

          //! The BFI semantics.
          void bfi_s(triton::arch::Instruction& inst);

          //! The BIC semantics.
          void bic_s(triton::arch::Instruction& inst);

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

          //! The CCMP semantics
          void ccmp_s(triton::arch::Instruction& inst);

          //! The CINC semantics
          void cinc_s(triton::arch::Instruction& inst);

          //! The CLZ semantics
          void clz_s(triton::arch::Instruction& inst);

          //! The CMN semantics
          void cmn_s(triton::arch::Instruction& inst);

          //! The CMP semantics
          void cmp_s(triton::arch::Instruction& inst);

          //! The CSEL semantics
          void csel_s(triton::arch::Instruction& inst);

          //! The CSET semantics
          void cset_s(triton::arch::Instruction& inst);

          //! The CSINC semantics
          void csinc_s(triton::arch::Instruction& inst);

          //! The CSNEG semantics
          void csneg_s(triton::arch::Instruction& inst);

          //! The EON semantics.
          void eon_s(triton::arch::Instruction& inst);

          //! The EOR semantics.
          void eor_s(triton::arch::Instruction& inst);

          //! The EXTR semantics.
          void extr_s(triton::arch::Instruction& inst);

          //! The LDAR semantics.
          void ldar_s(triton::arch::Instruction& inst);

          //! The LDARB semantics.
          void ldarb_s(triton::arch::Instruction& inst);

          //! The LDARH semantics.
          void ldarh_s(triton::arch::Instruction& inst);

          //! The LDAXR semantics.
          void ldaxr_s(triton::arch::Instruction& inst);

          //! The LDAXRB semantics.
          void ldaxrb_s(triton::arch::Instruction& inst);

          //! The LDAXRH semantics.
          void ldaxrh_s(triton::arch::Instruction& inst);

          //! The LDP semantics.
          void ldp_s(triton::arch::Instruction& inst);

          //! The LDR semantics.
          void ldr_s(triton::arch::Instruction& inst);

          //! The LDRB semantics.
          void ldrb_s(triton::arch::Instruction& inst);

          //! The LDRH semantics.
          void ldrh_s(triton::arch::Instruction& inst);

          //! The LDRSB semantics.
          void ldrsb_s(triton::arch::Instruction& inst);

          //! The LDRSH semantics.
          void ldrsh_s(triton::arch::Instruction& inst);

          //! The LDRSW semantics.
          void ldrsw_s(triton::arch::Instruction& inst);

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

          //! The LDXR semantics.
          void ldxr_s(triton::arch::Instruction& inst);

          //! The LDXRB semantics.
          void ldxrb_s(triton::arch::Instruction& inst);

          //! The LDXRH semantics.
          void ldxrh_s(triton::arch::Instruction& inst);

          //! The LSL semantics.
          void lsl_s(triton::arch::Instruction& inst);

          //! The LSR semantics.
          void lsr_s(triton::arch::Instruction& inst);

          //! The MADD semantics.
          void madd_s(triton::arch::Instruction& inst);

          //! The MNEG semantics.
          void mneg_s(triton::arch::Instruction& inst);

          //! The MOV semantics.
          void mov_s(triton::arch::Instruction& inst);

          //! The MOVK semantics.
          void movk_s(triton::arch::Instruction& inst);

          //! The MOVN semantics.
          void movn_s(triton::arch::Instruction& inst);

          //! The MOVZ semantics.
          void movz_s(triton::arch::Instruction& inst);

          //! The MSUB semantics.
          void msub_s(triton::arch::Instruction& inst);

          //! The MUL semantics.
          void mul_s(triton::arch::Instruction& inst);

          //! The MVN semantics.
          void mvn_s(triton::arch::Instruction& inst);

          //! The NEG semantics.
          void neg_s(triton::arch::Instruction& inst);

          //! The NOP semantics.
          void nop_s(triton::arch::Instruction& inst);

          //! The ORN semantics.
          void orn_s(triton::arch::Instruction& inst);

          //! The ORR semantics.
          void orr_s(triton::arch::Instruction& inst);

          //! The RBIT semantics.
          void rbit_s(triton::arch::Instruction& inst);

          //! The RET semantics.
          void ret_s(triton::arch::Instruction& inst);

          //! The REV semantics.
          void rev_s(triton::arch::Instruction& inst);

          //! The REV16 semantics.
          void rev16_s(triton::arch::Instruction& inst);

          //! The REV32 semantics.
          void rev32_s(triton::arch::Instruction& inst);

          //! The ROR semantics.
          void ror_s(triton::arch::Instruction& inst);

          //! The SBFX semantics.
          void sbfx_s(triton::arch::Instruction& inst);

          //! The SDIV semantics.
          void sdiv_s(triton::arch::Instruction& inst);

          //! The SMADDL semantics.
          void smaddl_s(triton::arch::Instruction& inst);

          //! The SMSUBL semantics.
          void smsubl_s(triton::arch::Instruction& inst);

          //! The SMULH semantics.
          void smulh_s(triton::arch::Instruction& inst);

          //! The SMULL semantics.
          void smull_s(triton::arch::Instruction& inst);

          //! The STLR semantics.
          void stlr_s(triton::arch::Instruction& inst);

          //! The STLRB semantics.
          void stlrb_s(triton::arch::Instruction& inst);

          //! The STLRH semantics.
          void stlrh_s(triton::arch::Instruction& inst);

          //! The STP semantics.
          void stp_s(triton::arch::Instruction& inst);

          //! The STR semantics.
          void str_s(triton::arch::Instruction& inst);

          //! The STRB semantics.
          void strb_s(triton::arch::Instruction& inst);

          //! The STRH semantics.
          void strh_s(triton::arch::Instruction& inst);

          //! The STUR semantics.
          void stur_s(triton::arch::Instruction& inst);

          //! The STURB semantics.
          void sturb_s(triton::arch::Instruction& inst);

          //! The STURH semantics.
          void sturh_s(triton::arch::Instruction& inst);

          //! The SUB semantics.
          void sub_s(triton::arch::Instruction& inst);

          //! The SVC semantics.
          void svc_s(triton::arch::Instruction& inst);

          //! The SXTB semantics.
          void sxtb_s(triton::arch::Instruction& inst);

          //! The SXTH semantics.
          void sxth_s(triton::arch::Instruction& inst);

          //! The SXTW semantics.
          void sxtw_s(triton::arch::Instruction& inst);

          //! The TBNZ semantics.
          void tbnz_s(triton::arch::Instruction& inst);

          //! The TBZ semantics.
          void tbz_s(triton::arch::Instruction& inst);

          //! The TST semantics.
          void tst_s(triton::arch::Instruction& inst);

          //! The UBFIZ semantics.
          void ubfiz_s(triton::arch::Instruction& inst);

          //! The UBFX semantics.
          void ubfx_s(triton::arch::Instruction& inst);

          //! The UDIV semantics.
          void udiv_s(triton::arch::Instruction& inst);

          //! The UMADDL semantics.
          void umaddl_s(triton::arch::Instruction& inst);

          //! The UMNEGL semantics.
          void umnegl_s(triton::arch::Instruction& inst);

          //! The UMSUBL semantics.
          void umsubl_s(triton::arch::Instruction& inst);

          //! The UMULH semantics.
          void umulh_s(triton::arch::Instruction& inst);

          //! The UMULL semantics.
          void umull_s(triton::arch::Instruction& inst);

          //! The UXTB semantics.
          void uxtb_s(triton::arch::Instruction& inst);

          //! The UXTH semantics.
          void uxth_s(triton::arch::Instruction& inst);
      };

    /*! @} End of aarch64 namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_AARCH64SEMANTICS_H */
