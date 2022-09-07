//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_ARM32SEMANTICS_H
#define TRITON_ARM32SEMANTICS_H

#include <triton/archEnums.hpp>
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

    //! The ARM namespace
    namespace arm {
    /*!
     *  \ingroup arch
     *  \addtogroup arm
     *  @{
     */

      //! The arm32 namespace
      namespace arm32 {
      /*!
       *  \ingroup arm
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

            //! Exception status
            triton::arch::exception_e exception;

          public:
            //! Constructor.
            TRITON_EXPORT Arm32Semantics(triton::arch::Architecture* architecture,
                                         triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                                         triton::engines::taint::TaintEngine* taintEngine,
                                         const triton::ast::SharedAstContext& astCtxt);

            //! Builds the semantics of the instruction. Returns `triton::arch::NO_FAULT` if succeed.
            TRITON_EXPORT triton::arch::exception_e buildSemantics(triton::arch::Instruction& inst);

          private:
            //! Rotates right.
            triton::uint32 ror(triton::uint32 value, triton::uint32 count);

            //! Execution state update semantics.
            void updateExecutionState(triton::arch::OperandWrapper& dst, const triton::ast::SharedAbstractNode& node);

            //! Exchanges instrution set according to provide operand.
            void exchangeInstructionSet(triton::arch::OperandWrapper& op, const triton::ast::SharedAbstractNode& node);

            //! Builds the semantics of a conditional instruction.
            triton::ast::SharedAbstractNode buildConditionalSemantics(triton::arch::Instruction& inst, triton::arch::OperandWrapper& dst, const triton::ast::SharedAbstractNode& opNode);

            //! Returns the AST corresponding to the adjustment of the LSB of the provided node.
            triton::ast::SharedAbstractNode adjustISSB(const triton::ast::SharedAbstractNode& node);

            //! Returns the AST corresponding to the clearing of the LSB of the provided node.
            triton::ast::SharedAbstractNode clearISSB(const triton::ast::SharedAbstractNode& node);

            //! Returns the AST corresponding to the Arm32 source base operand (it does not include the shift).
            triton::ast::SharedAbstractNode getArm32SourceBaseOperandAst(triton::arch::Instruction& inst, triton::arch::OperandWrapper& op);

            //! Returns the AST corresponding to the Arm32 source operand.
            triton::ast::SharedAbstractNode getArm32SourceOperandAst(triton::arch::Instruction& inst, triton::arch::OperandWrapper& op);

            //! Aligns the stack (add). Returns the new stack value.
            triton::uint64 alignAddStack_s(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& cond, triton::uint32 delta);

            //! Aligns the stack (sub). Returns the new stack value.
            triton::uint64 alignSubStack_s(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& cond, triton::uint32 delta);

            //! Creates a conditional node.
            triton::ast::SharedAbstractNode getCodeConditionAst(triton::arch::Instruction& inst);

            //! Control flow semantics. Used to represent PC.
            void controlFlow_s(triton::arch::Instruction& inst);

            //! Control flow semantics. Used to represent PC.
            void controlFlow_s(triton::arch::Instruction& inst,
                               const triton::ast::SharedAbstractNode& cond,
                               triton::arch::OperandWrapper& dst);

            //! Control flow semantics. Used to represent PC.
            void controlFlow_s(triton::arch::Instruction& inst,
                               const triton::ast::SharedAbstractNode& cond,
                               triton::arch::OperandWrapper& dst1,
                               triton::arch::OperandWrapper& dst2);

            //! Gets the taint state (based on flags) of a conditional instruction.
            bool getCodeConditionTaintState(const triton::arch::Instruction& inst);

            //! Spreads taint based considering conditional execution.
            void spreadTaint(triton::arch::Instruction& inst,
                             const triton::ast::SharedAbstractNode& cond,
                             const triton::engines::symbolic::SharedSymbolicExpression& expr,
                             const triton::arch::OperandWrapper& operand,
                             bool taint);

            /* Generic flags computation ------------------------------------- */

            //! The NF semantics.
            void nf_s(triton::arch::Instruction& inst,
                      const triton::ast::SharedAbstractNode& cond,
                      const triton::engines::symbolic::SharedSymbolicExpression& parent,
                      triton::arch::OperandWrapper& dst);

            //! The ZF semantics.
            void zf_s(triton::arch::Instruction& inst,
                      const triton::ast::SharedAbstractNode& cond,
                      const triton::engines::symbolic::SharedSymbolicExpression& parent,
                      triton::arch::OperandWrapper& dst);

            /* Specific flags computation ------------------------------------ */

            //! The CF semantics for the ADDS operation.
            void cfAdd_s(triton::arch::Instruction& inst,
                         const triton::ast::SharedAbstractNode& cond,
                         const triton::engines::symbolic::SharedSymbolicExpression& parent,
                         triton::arch::OperandWrapper& dst,
                         triton::ast::SharedAbstractNode& op1,
                         triton::ast::SharedAbstractNode& op2);

            //! The CF semantics for the SUBS operation.
            void cfSub_s(triton::arch::Instruction& inst,
                         const triton::ast::SharedAbstractNode& cond,
                         const triton::engines::symbolic::SharedSymbolicExpression& parent,
                         triton::arch::OperandWrapper& dst,
                         triton::ast::SharedAbstractNode& op1,
                         triton::ast::SharedAbstractNode& op2);

            //! The NF semantics for the SMULL operation.
            void nfSmull_s(triton::arch::Instruction& inst,
                           const triton::ast::SharedAbstractNode& cond,
                           const triton::engines::symbolic::SharedSymbolicExpression& parent1,
                           const triton::engines::symbolic::SharedSymbolicExpression& parent2,
                           triton::arch::OperandWrapper& dst1,
                           triton::arch::OperandWrapper& dst2);

            //! The ZF semantics for the SMULL operation.
            void zfSmull_s(triton::arch::Instruction& inst,
                           const triton::ast::SharedAbstractNode& cond,
                           const triton::engines::symbolic::SharedSymbolicExpression& parent1,
                           const triton::engines::symbolic::SharedSymbolicExpression& parent2,
                           triton::arch::OperandWrapper& dst1,
                           triton::arch::OperandWrapper& dst2);

            //! The VF semantics for the ADDS operation.
            void vfAdd_s(triton::arch::Instruction& inst,
                         const triton::ast::SharedAbstractNode& cond,
                         const triton::engines::symbolic::SharedSymbolicExpression& parent,
                         triton::arch::OperandWrapper& dst,
                         triton::ast::SharedAbstractNode& op1,
                         triton::ast::SharedAbstractNode& op2);

            //! The VF semantics for the SUBS operation.
            void vfSub_s(triton::arch::Instruction& inst,
                         const triton::ast::SharedAbstractNode& cond,
                         const triton::engines::symbolic::SharedSymbolicExpression& parent,
                         triton::arch::OperandWrapper& dst,
                         triton::ast::SharedAbstractNode& op1,
                         triton::ast::SharedAbstractNode& op2);

            //! The CF semantics for bitwise operations (AND, BIC, EOR, MVN, ORR, ORN and TST).
            void cfBitwise_s(triton::arch::Instruction& inst,
                             const triton::ast::SharedAbstractNode& cond,
                             const triton::engines::symbolic::SharedSymbolicExpression& parent,
                             triton::arch::OperandWrapper& src);

            //! The CF semantics for shift operations (ASR, LSL, LSR, ROR and RRX).
            void cfShift_s(triton::arch::Instruction& inst,
                           const triton::ast::SharedAbstractNode& cond,
                           const triton::engines::symbolic::SharedSymbolicExpression& parent,
                           const triton::ast::SharedAbstractNode& op1,
                           triton::arch::OperandWrapper& src,
                           const triton::arch::arm::shift_e type);

            //! The CF semantics for the ASR operation.
            void cfAsr_s(triton::arch::Instruction& inst,
                         const triton::ast::SharedAbstractNode& cond,
                         const triton::engines::symbolic::SharedSymbolicExpression& parent,
                         const triton::ast::SharedAbstractNode& op1,
                         triton::arch::OperandWrapper& src);

            //! The CF semantics for the LSL operation.
            void cfLsl_s(triton::arch::Instruction& inst,
                         const triton::ast::SharedAbstractNode& cond,
                         const triton::engines::symbolic::SharedSymbolicExpression& parent,
                         const triton::ast::SharedAbstractNode& op1,
                         triton::arch::OperandWrapper& src);

            //! The CF semantics for the LSR operation.
            void cfLsr_s(triton::arch::Instruction& inst,
                         const triton::ast::SharedAbstractNode& cond,
                         const triton::engines::symbolic::SharedSymbolicExpression& parent,
                         const triton::ast::SharedAbstractNode& op1,
                         triton::arch::OperandWrapper& src);

            //! The CF semantics for the ROR operation.
            void cfRor_s(triton::arch::Instruction& inst,
                         const triton::ast::SharedAbstractNode& cond,
                         const triton::engines::symbolic::SharedSymbolicExpression& parent,
                         const triton::ast::SharedAbstractNode& op1,
                         triton::arch::OperandWrapper& src);

            //! The CF semantics for the RRX operation.
            void cfRrx_s(triton::arch::Instruction& inst,
                         const triton::ast::SharedAbstractNode& cond,
                         const triton::engines::symbolic::SharedSymbolicExpression& parent,
                         const triton::ast::SharedAbstractNode& op1,
                         triton::arch::OperandWrapper& src);

            //! The CF semantics for bitwise and shift operations.
            triton::ast::SharedAbstractNode getShiftCAst(const triton::ast::SharedAbstractNode& node,
                                                         const triton::arch::arm::shift_e type,
                                                         const triton::ast::SharedAbstractNode& shiftAmount);

            //! Auxiliary function for the CF semantics for bitwise and shift operations.
            triton::arch::arm::shift_e getShiftCBaseType(const triton::arch::arm::ArmOperandProperties& shift);

            //! Auxiliary function for the CF semantics for bitwise and shift operations.
            triton::ast::SharedAbstractNode getShiftCAmountAst(const triton::arch::arm::ArmOperandProperties& shift);

            /* Instruction semantics ----------------------------------------- */

            //! The ADC semantics.
            void adc_s(triton::arch::Instruction& inst);

            //! The ADD semantics.
            void add_s(triton::arch::Instruction& inst);

            //! The ADR semantics.
            void adr_s(triton::arch::Instruction& inst);

            //! The AND semantics.
            void and_s(triton::arch::Instruction& inst);

            //! The ASR semantics.
            void asr_s(triton::arch::Instruction& inst);

            //! The B semantics.
            void b_s(triton::arch::Instruction& inst);

            //! The BFC semantics.
            void bfc_s(triton::arch::Instruction& inst);

            //! The BFI semantics.
            void bfi_s(triton::arch::Instruction& inst);

            //! The BIC semantics.
            void bic_s(triton::arch::Instruction& inst);

            //! The BL(X) semantics.
            void bl_s(triton::arch::Instruction& inst, bool exchange);

            //! The BX semantics.
            void bx_s(triton::arch::Instruction& inst);

            //! The CBZ semantics.
            void cbz_s(triton::arch::Instruction& inst);

            //! The CBNZ semantics.
            void cbnz_s(triton::arch::Instruction& inst);

            //! The CLZ semantics.
            void clz_s(triton::arch::Instruction& inst);

            //! The CMN semantics.
            void cmn_s(triton::arch::Instruction& inst);

            //! The CMP semantics.
            void cmp_s(triton::arch::Instruction& inst);

            //! The EOR semantics.
            void eor_s(triton::arch::Instruction& inst);

            //! The IT semantics.
            void it_s(triton::arch::Instruction& inst);

            //! The LDM semantics.
            void ldm_s(triton::arch::Instruction& inst);

            //! The LDR semantics.
            void ldr_s(triton::arch::Instruction& inst);

            //! The LDRB semantics.
            void ldrb_s(triton::arch::Instruction& inst);

            //! The LDREX semantics.
            void ldrex_s(triton::arch::Instruction& inst);

            //! The LDRH semantics.
            void ldrh_s(triton::arch::Instruction& inst);

            //! The LDRSB semantics.
            void ldrsb_s(triton::arch::Instruction& inst);

            //! The LDRSH semantics.
            void ldrsh_s(triton::arch::Instruction& inst);

            //! The LDRD semantics.
            void ldrd_s(triton::arch::Instruction& inst);

            //! The LSL semantics.
            void lsl_s(triton::arch::Instruction& inst);

            //! The LSR semantics.
            void lsr_s(triton::arch::Instruction& inst);

            //! The MLA semantics.
            void mla_s(triton::arch::Instruction& inst);

            //! The MLS semantics.
            void mls_s(triton::arch::Instruction& inst);

            //! The MOV semantics.
            void mov_s(triton::arch::Instruction& inst);

            //! The MOVT semantics.
            void movt_s(triton::arch::Instruction& inst);

            //! The MUL semantics.
            void mul_s(triton::arch::Instruction& inst);

            //! The MVN semantics.
            void mvn_s(triton::arch::Instruction& inst);

            //! The NOP semantics.
            void nop_s(triton::arch::Instruction& inst);

            //! The ORN semantics.
            void orn_s(triton::arch::Instruction& inst);

            //! The ORR semantics.
            void orr_s(triton::arch::Instruction& inst);

            //! The POP semantics.
            void pop_s(triton::arch::Instruction& inst);

            //! The PUSH semantics.
            void push_s(triton::arch::Instruction& inst);

            //! The RBIT semantics.
            void rbit_s(triton::arch::Instruction& inst);

            //! The REV16 semantics.
            void rev16_s(triton::arch::Instruction& inst);

            //! The REV semantics.
            void rev_s(triton::arch::Instruction& inst);

            //! The ROR semantics.
            void ror_s(triton::arch::Instruction& inst);

            //! The RRX semantics.
            void rrx_s(triton::arch::Instruction& inst);

            //! The RSB semantics.
            void rsb_s(triton::arch::Instruction& inst);

            //! The RSC semantics.
            void rsc_s(triton::arch::Instruction& inst);

            //! The SBC semantics.
            void sbc_s(triton::arch::Instruction& inst);

            //! The SBFX semantics.
            void sbfx_s(triton::arch::Instruction& inst);

            //! The SDIV semantics.
            void sdiv_s(triton::arch::Instruction& inst);

            //! The SMLABB semantics.
            void smlabb_s(triton::arch::Instruction& inst);

            //! The SMLABT semantics.
            void smlabt_s(triton::arch::Instruction& inst);

            //! The SMLATB semantics.
            void smlatb_s(triton::arch::Instruction& inst);

            //! The SMLATT semantics.
            void smlatt_s(triton::arch::Instruction& inst);

            //! The SMULL semantics.
            void smull_s(triton::arch::Instruction& inst);

            //! The STM semantics.
            void stm_s(triton::arch::Instruction& inst);

            //! The STMIB semantics.
            void stmib_s(triton::arch::Instruction& inst);

            //! The STR semantics.
            void str_s(triton::arch::Instruction& inst);

            //! The STRB semantics.
            void strb_s(triton::arch::Instruction& inst);

            //! The STRD semantics.
            void strd_s(triton::arch::Instruction& inst);

            //! The STREX semantics.
            void strex_s(triton::arch::Instruction& inst);

            //! The STRH semantics.
            void strh_s(triton::arch::Instruction& inst);

            //! The SUB semantics.
            void sub_s(triton::arch::Instruction& inst);

            //! The SXTB semantics.
            void sxtb_s(triton::arch::Instruction &inst);

            //! The SXTH semantics.
            void sxth_s(triton::arch::Instruction &inst);

            //! The TST semantics.
            void tst_s(triton::arch::Instruction& inst);

            //! The TBB semantics.
            void tbb_s(triton::arch::Instruction& inst);

            //! The TEQ semantics.
            void teq_s(triton::arch::Instruction& inst);

            //! The UBFX semantics.
            void ubfx_s(triton::arch::Instruction &inst);

            //! The UDIV semantics.
            void udiv_s(triton::arch::Instruction& inst);

            //! The UMULL semantics.
            void umull_s(triton::arch::Instruction& inst);

            //! The UXTB semantics.
            void uxtb_s(triton::arch::Instruction & inst);

            //! The UXTH semantics.
            void uxth_s(triton::arch::Instruction & inst);

        };

      /*! @} End of arm32 namespace */
      };
    /*! @} End of arm namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ARM32SEMANTICS_H */
