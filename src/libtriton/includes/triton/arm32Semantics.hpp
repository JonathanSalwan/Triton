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

          public:
            //! Constructor.
            TRITON_EXPORT Arm32Semantics(triton::arch::Architecture* architecture,
                                         triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                                         triton::engines::taint::TaintEngine* taintEngine,
                                         const triton::ast::SharedAstContext& astCtxt);

            //! Builds the semantics of the instruction. Returns true if the instruction is supported.
            TRITON_EXPORT bool buildSemantics(triton::arch::Instruction& inst);

          private:
            //! Builds the semantics of a conditional instruction.
            triton::ast::SharedAbstractNode buildConditionalSemantics(triton::arch::Instruction& inst,
                                                                      triton::arch::OperandWrapper& dst,
                                                                      const triton::ast::SharedAbstractNode& opNode);

            //! Execution state update semantics.
            void updateExecutionState(triton::arch::OperandWrapper& dst,
                                      const triton::ast::SharedAbstractNode& node);

            //! Exchanges instrution set according to provide operand.
            void exchangeInstructionSet(triton::arch::OperandWrapper& op,
                                        const triton::ast::SharedAbstractNode& node);

            //! Returns the AST corresponding to the adjustment of the LSB of the provided node.
            triton::ast::SharedAbstractNode adjustISSB(const triton::ast::SharedAbstractNode& node);

            //! Returns the AST corresponding to the clearing of the LSB of the provided node.
            triton::ast::SharedAbstractNode clearISSB(const triton::ast::SharedAbstractNode& node);

            //! Rotates right.
            uint32_t ror(uint32_t value, unsigned int count);

            //! Returns the AST corresponding to the Arm32 source base operand (it does not include the shift).
            triton::ast::SharedAbstractNode getArm32SourceBaseOperandAst(triton::arch::Instruction& inst,
                                                                         triton::arch::OperandWrapper& op);

            //! Returns the AST corresponding to the Arm32 source operand.
            triton::ast::SharedAbstractNode getArm32SourceOperandAst(triton::arch::Instruction& inst,
                                                                     triton::arch::OperandWrapper& op);

            //! Aligns the stack (add). Returns the new stack value.
            triton::uint64 alignAddStack_s(triton::arch::Instruction& inst,
                                           const triton::ast::SharedAbstractNode& cond,
                                           triton::uint32 delta);

            //! Aligns the stack (sub). Returns the new stack value.
            triton::uint64 alignSubStack_s(triton::arch::Instruction& inst,
                                           const triton::ast::SharedAbstractNode& cond,
                                           triton::uint32 delta);

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

            //! Creates a conditional node.
            triton::ast::SharedAbstractNode getCodeConditionAst(triton::arch::Instruction& inst);

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

            //! Auxiliary function for the CF semantics for bitwise and shift operations.
            triton::ast::SharedAbstractNode lsl_c(const triton::ast::SharedAbstractNode& node, uint32 shift);

            //! Auxiliary function for the CF semantics for bitwise and shift operations.
            triton::ast::SharedAbstractNode lsl(const triton::ast::SharedAbstractNode& node, uint32 shift);

            //! Auxiliary function for the CF semantics for bitwise and shift operations.
            triton::ast::SharedAbstractNode lsr_c(const triton::ast::SharedAbstractNode& node, uint32 shift);

            //! Auxiliary function for the CF semantics for bitwise and shift operations.
            triton::ast::SharedAbstractNode lsr(const triton::ast::SharedAbstractNode& node, uint32 shift);

            //! Auxiliary function for the CF semantics for bitwise and shift operations.
            triton::ast::SharedAbstractNode ror_c(const triton::ast::SharedAbstractNode& node, uint32 shift);

            //! Auxiliary function for the CF semantics for bitwise and shift operations.
            triton::ast::SharedAbstractNode ror(const triton::ast::SharedAbstractNode& node, uint32 shift);

            /* Instruction semantics ----------------------------------------- */

            //! The ADC semantics.
            void adc_s(triton::arch::Instruction& inst);

            //! The ADD semantics.
            void add_s(triton::arch::Instruction& inst);

            //! The AND semantics.
            void and_s(triton::arch::Instruction& inst);

            //! The ASR semantics.
            void asr_s(triton::arch::Instruction& inst);

            //! The B semantics.
            void b_s(triton::arch::Instruction& inst);

            //! The BIC semantics.
            void bic_s(triton::arch::Instruction& inst);

            //! The BL(X) semantics.
            void bl_s(triton::arch::Instruction& inst, bool exchange);

            //! The BX semantics.
            void bx_s(triton::arch::Instruction& inst);

            //! The CBZ semantics.
            void cbz_s(triton::arch::Instruction& inst);

            //! The CLZ semantics.
            void clz_s(triton::arch::Instruction& inst);

            //! The CMP semantics.
            void cmp_s(triton::arch::Instruction& inst);

            //! The EOR semantics.
            void eor_s(triton::arch::Instruction& inst);

            //! The LDM semantics.
            void ldm_s(triton::arch::Instruction& inst);

            //! The LDR semantics.
            void ldr_s(triton::arch::Instruction& inst);

            //! The LDRB semantics.
            void ldrb_s(triton::arch::Instruction& inst);

            //! The LDRD semantics.
            void ldrd_s(triton::arch::Instruction& inst);

            //! The LSL semantics.
            void lsl_s(triton::arch::Instruction& inst);

            //! The LSR semantics.
            void lsr_s(triton::arch::Instruction& inst);

            //! The MOV semantics.
            void mov_s(triton::arch::Instruction& inst);

            //! The MUL semantics.
            void mul_s(triton::arch::Instruction& inst);

            //! The MVN semantics.
            void mvn_s(triton::arch::Instruction& inst);

            //! The ORR semantics.
            void orr_s(triton::arch::Instruction& inst);

            //! The POP semantics.
            void pop_s(triton::arch::Instruction& inst);

            //! The PUSH semantics.
            void push_s(triton::arch::Instruction& inst);

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

            //! The STRH semantics.
            void strh_s(triton::arch::Instruction& inst);

            //! The SUB semantics.
            void sub_s(triton::arch::Instruction& inst);

            //! The TST semantics.
            void tst_s(triton::arch::Instruction& inst);
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
