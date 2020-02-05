//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <utility>

#include <triton/arm32Cpu.hpp>
#include <triton/arm32Semantics.hpp>
#include <triton/arm32Specifications.hpp>
#include <triton/astContext.hpp>
#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>



/*! \page SMT_arm32_Semantics_Supported_page ARM32 SMT semantics supported
    \brief [**internal**] List of the supported semantics for the ARM32 architecture.


Mnemonic                      | Description
------------------------------|------------
ADC                           | Add with Carry
ADD                           | Add
ADDW                          | Add
AND                           | Bitwise AND
ASR                           | Arithmetic Shift Right
B                             | Branch
BIC                           | Bitwise Bit Clear
BL                            | Branch with Link
BLX                           | Branch with Link and Exchange
BX                            | Branch and Exchange
CBZ                           | Compare and Branch on Zero
CLZ                           | Count Leading Zeros
CMP                           | Compare
EOR                           | Bitwise Exclusive OR
LDM                           | Load Multiple Registers
LDR                           | Load Register
LDRB                          | Load Register Byte
LDRD                          | Load Register Dual
LSL                           | Logical Shift Left
LSR                           | Logical Shift Right
MOV                           | Move Register
MOVW                          | Move Register
MUL                           | Multiply
MVN                           | Bitwise NOT
ORR                           | Bitwise OR
POP                           | Pop Multiple Registers
PUSH                          | Push Multiple Registers
REV                           | Byte-Reverse Word
ROR                           | Rotate Right
RRX                           | Rotate Right with Extend
RSB                           | Reverse Subtract
RSC                           | Reverse Subtract with Carry
SBC                           | Subtract with Carry
SMULL                         | Signed Multiply Long
STM                           | Store Multiple Registers
STMIB                         | Store Multiple Increment Before
STR                           | Store Register
STRB                          | Store Register Byte
STRD                          | Store Register Dual
STRH                          | Store Register Halfword
SUB                           | Substract
TST                           | Test

*/



namespace triton {
  namespace arch {
    namespace arm {
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
          switch (inst.getType()) {
            case ID_INS_ADC:       this->adc_s(inst);           break;
            case ID_INS_ADD:       this->add_s(inst);           break;
            case ID_INS_ADDW:      this->add_s(inst);           break;
            case ID_INS_AND:       this->and_s(inst);           break;
            case ID_INS_ASR:       this->asr_s(inst);           break;
            case ID_INS_B:         this->b_s(inst);             break;
            case ID_INS_BIC:       this->bic_s(inst);           break;
            case ID_INS_BL:        this->bl_s(inst, false);     break;
            case ID_INS_BLX:       this->bl_s(inst, true);      break;
            case ID_INS_BX:        this->bx_s(inst);            break;
            case ID_INS_CBZ:       this->cbz_s(inst);           break;
            case ID_INS_CLZ:       this->clz_s(inst);           break;
            case ID_INS_CMP:       this->cmp_s(inst);           break;
            case ID_INS_EOR:       this->eor_s(inst);           break;
            case ID_INS_LDM:       this->ldm_s(inst);           break;
            case ID_INS_LDR:       this->ldr_s(inst);           break;
            case ID_INS_LDRB:      this->ldrb_s(inst);          break;
            case ID_INS_LDRD:      this->ldrd_s(inst);          break;
            case ID_INS_LSL:       this->lsl_s(inst);           break;
            case ID_INS_LSR:       this->lsr_s(inst);           break;
            case ID_INS_MOV:       this->mov_s(inst);           break;
            case ID_INS_MOVW:      this->mov_s(inst);           break;
            case ID_INS_MUL:       this->mul_s(inst);           break;
            case ID_INS_MVN:       this->mvn_s(inst);           break;
            case ID_INS_ORR:       this->orr_s(inst);           break;
            case ID_INS_POP:       this->pop_s(inst);           break;
            case ID_INS_PUSH:      this->push_s(inst);          break;
            case ID_INS_REV:       this->rev_s(inst);           break;
            case ID_INS_ROR:       this->ror_s(inst);           break;
            case ID_INS_RRX:       this->rrx_s(inst);           break;
            case ID_INS_RSB:       this->rsb_s(inst);           break;
            case ID_INS_RSC:       this->rsc_s(inst);           break;
            case ID_INS_SBC:       this->sbc_s(inst);           break;
            case ID_INS_SMULL:     this->smull_s(inst);         break;
            case ID_INS_STM:       this->stm_s(inst);           break;
            case ID_INS_STMIB:     this->stmib_s(inst);         break;
            case ID_INS_STR:       this->str_s(inst);           break;
            case ID_INS_STRB:      this->strb_s(inst);          break;
            case ID_INS_STRD:      this->strd_s(inst);          break;
            case ID_INS_STRH:      this->strh_s(inst);          break;
            case ID_INS_SUB:       this->sub_s(inst);           break;
            case ID_INS_TST:       this->tst_s(inst);           break;
            default:
              return false;
          }
          return true;
        }


        inline triton::ast::SharedAbstractNode Arm32Semantics::buildConditionalSemantics(triton::arch::Instruction& inst,
                                                                                         triton::arch::OperandWrapper& dst,
                                                                                         const triton::ast::SharedAbstractNode& opNode) {
          /* IMPORTANT NOTE The condition node should be built first, before
           * any other node that may use the flags. The reason for this is that
           * the condition node require the original values of the flags,
           * otherwise the result would not be as the expected.
           */
          auto condNode = this->getCodeConditionAst(inst);
          auto thenNode = opNode;
          auto elseNode = this->symbolicEngine->getOperandAst(inst, dst);

          if (dst.getRegister().getId() == ID_REG_ARM32_PC) {
            thenNode = this->clearISSB(opNode);
          }

          return this->astCtxt->ite(condNode, thenNode, elseNode);
        }


        inline void Arm32Semantics::updateExecutionState(triton::arch::OperandWrapper& dst,
                                                         const triton::ast::SharedAbstractNode& node) {
          /* NOTE: In case the PC register is used as the destination operand,
           * check whether there is a mode switch.
           */
          if (dst.getRegister().getId() == ID_REG_ARM32_PC) {
            this->exchangeInstructionSet(dst, node);
          }
        }


        inline void Arm32Semantics::exchangeInstructionSet(triton::arch::OperandWrapper& op,
                                                           const triton::ast::SharedAbstractNode& node) {
          /* NOTE: There are two possibilities, depending on the operand. If it
           * is an immediate, there is a mode switch (that is, if it is currently
           * in ARM mode it switches to Thumb and the other way around). In
           * case the operand is a register, it switches mode according to the
           * instruction set selection bit (LSB) of the register.
           */
          auto cpu = static_cast<triton::arch::arm::arm32::Arm32Cpu*>(this->architecture->getCpuInstance());
          bool state;

          switch (op.getType()) {
            case triton::arch::OP_IMM:
              state = !cpu->isThumb();
              break;
            case triton::arch::OP_REG:
              state = (node->evaluate() & 0x1) == 0x1;
              break;
            default:
              throw triton::exceptions::Semantics("Arm32Semantics::Arm32Semantics(): Invalid operand type.");
          }

          cpu->setThumb(state);
        }


        inline triton::ast::SharedAbstractNode Arm32Semantics::adjustISSB(const triton::ast::SharedAbstractNode& node) {
          /* Set instruction set selection bit (LSB) according to the current
           * execution mode.
           */
          auto thumb = static_cast<triton::arch::arm::arm32::Arm32Cpu*>(this->architecture->getCpuInstance())->isThumb();

          return this->astCtxt->bvor(node, this->astCtxt->bv(thumb ? 1 : 0, node->getBitvectorSize()));
        }


        inline triton::ast::SharedAbstractNode Arm32Semantics::clearISSB(const triton::ast::SharedAbstractNode& node) {
          /* Clear instruction set selection bit (LSB). */
          auto mask = this->astCtxt->bv(node->getBitvectorMask()-1, node->getBitvectorSize());

          return this->astCtxt->bvand(node, mask);
        }


        uint32_t Arm32Semantics::ror(uint32_t value, unsigned int count) {
          const unsigned int mask = 8 * sizeof(value) - 1;
          unsigned int sr_count = count & mask;
          unsigned int sl_count = (-count) & mask;
          return (value >> sr_count) | (value << sl_count);
        }

        inline triton::ast::SharedAbstractNode Arm32Semantics::getArm32SourceBaseOperandAst(triton::arch::Instruction& inst,
                                                                                            triton::arch::OperandWrapper& op) {
          /* NOTE: This is a hacky way to obtain the ast of the operand
           * without the shift. This has to be done before building the
           * semantics (the current value is needed, not the new one).
           */
          /* TODO (cnheitman): Discuss. Should we deal with this here (and in
           * this way) or move it to the Symbolic Engine. See also
           * `getArm32SourceOperandAst` and its use of `getShiftAst`.
           */
          if (op.getType() == triton::arch::OP_REG) {
            auto opBase = triton::arch::OperandWrapper(op.getRegister());
            opBase.getRegister().setShiftType(triton::arch::arm::ID_SHIFT_INVALID);
            return this->symbolicEngine->getOperandAst(inst, opBase);
          }

          throw triton::exceptions::Semantics("Arm32Semantics::getArm32SourceBaseOperandAst(): Invalid operand type.");
        }

        inline triton::ast::SharedAbstractNode Arm32Semantics::getArm32SourceOperandAst(triton::arch::Instruction& inst,
                                                                                        triton::arch::OperandWrapper& op) {
          /* This function is a wrapper for the getOperandAst function. It makes
           * sure to provide the correct value when reading the PC register. For
           * more information, refer to "PC, the program counter" description
           * within the "ARM core registers" section in the reference manual.
           */
          auto thumb  = static_cast<triton::arch::arm::arm32::Arm32Cpu*>(this->architecture->getCpuInstance())->isThumb();
          auto offset = thumb ? 4 : 8;
          auto node   = this->symbolicEngine->getOperandAst(inst, op);

          if (op.getType() == triton::arch::OP_REG && op.getRegister().getId() == ID_REG_ARM32_PC) {
            node = this->astCtxt->bv(inst.getAddress() + offset, op.getBitSize());

            /* Shift AST if it's a shift operand */
            /* TODO: Clean this and check if we can use the pcRelative thing
             * used for x86.
             */
            if (op.getRegister().getShiftType() != triton::arch::arm::ID_SHIFT_INVALID) {
              node = this->symbolicEngine->getShiftAst(static_cast<const triton::arch::arm::ArmOperandProperties>(op.getRegister()), node);
            }
          }

          return node;
        }


        triton::uint64 Arm32Semantics::alignAddStack_s(triton::arch::Instruction& inst,
                                                       const triton::ast::SharedAbstractNode& cond,
                                                       triton::uint32 delta) {
          auto dst = triton::arch::OperandWrapper(this->architecture->getStackPointer());

          /* Create symbolic operands */
          auto op1 = this->symbolicEngine->getOperandAst(inst, dst);
          auto op2 = this->astCtxt->bv(delta, dst.getBitSize());

          /* Create the semantics */
          auto node = this->astCtxt->ite(
                        cond,
                        this->astCtxt->bvadd(op1, op2),
                        op1
                      );

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "Stack alignment");

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->taintUnion(dst, dst));

          /* Return the new stack value */
          return node->evaluate().convert_to<triton::uint64>();
        }


        triton::uint64 Arm32Semantics::alignSubStack_s(triton::arch::Instruction& inst,
                                                       const triton::ast::SharedAbstractNode& cond,
                                                       triton::uint32 delta) {
          auto dst = triton::arch::OperandWrapper(this->architecture->getStackPointer());

          /* Create symbolic operands */
          auto op1 = this->symbolicEngine->getOperandAst(inst, dst);
          auto op2 = this->astCtxt->bv(delta, dst.getBitSize());

          /* Create the semantics */
          auto node = this->astCtxt->ite(
                        cond,
                        this->astCtxt->bvsub(op1, op2),
                        op1
                      );

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "Stack alignment");

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->taintUnion(dst, dst));

          /* Return the new stack value */
          return node->evaluate().convert_to<triton::uint64>();
        }


        void Arm32Semantics::controlFlow_s(triton::arch::Instruction& inst) {
          auto pc = triton::arch::OperandWrapper(this->architecture->getParentRegister(ID_REG_ARM32_PC));

          /* Create the semantics */
          auto node = this->astCtxt->bv(inst.getNextAddress(), pc.getBitSize());

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicRegisterExpression(inst, node, this->architecture->getParentRegister(ID_REG_ARM32_PC), "Program Counter");

          /* Spread taint */
          expr->isTainted = this->taintEngine->setTaintRegister(this->architecture->getParentRegister(ID_REG_ARM32_PC), triton::engines::taint::UNTAINTED);
        }


        void Arm32Semantics::controlFlow_s(triton::arch::Instruction& inst,
                                           const triton::ast::SharedAbstractNode& cond,
                                           triton::arch::OperandWrapper& dst) {
          /* NOTE: This version of Arm32Semantics::controlFlow_s should only be
           * used for instructions that use a destination register. In that case,
           * it check whether the destination is the PC and acts accordingly.
           * For example: ADD, SUB, etc.
           */
          auto pc = triton::arch::OperandWrapper(this->architecture->getParentRegister(ID_REG_ARM32_PC));

          triton::ast::SharedAbstractNode node;

          /* Create the semantics */
          if (cond->evaluate() == true && dst.getRegister().getId() == ID_REG_ARM32_PC) {
            node = this->symbolicEngine->getOperandAst(inst, pc);
          } else {
            node = this->astCtxt->bv(inst.getNextAddress(), pc.getBitSize());
          }

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicRegisterExpression(inst, node, this->architecture->getParentRegister(ID_REG_ARM32_PC), "Program Counter");

          /* Spread taint */
          expr->isTainted = this->taintEngine->setTaintRegister(this->architecture->getParentRegister(ID_REG_ARM32_PC), triton::engines::taint::UNTAINTED);
        }


        void Arm32Semantics::controlFlow_s(triton::arch::Instruction& inst,
                                           const triton::ast::SharedAbstractNode& cond,
                                           triton::arch::OperandWrapper& dst1,
                                           triton::arch::OperandWrapper& dst2) {

          /* NOTE: This version of Arm32Semantics::controlFlow_s should only be
           * used for instructions that use two destination registers. In that case,
           * it check whether any of the destination register is the PC and acts accordingly.
           * For example: SMULL.
           */
          auto pc = triton::arch::OperandWrapper(this->architecture->getParentRegister(ID_REG_ARM32_PC));

          triton::ast::SharedAbstractNode node;

          /* Create the semantics */
          if (cond->evaluate() == true && (dst1.getRegister().getId() == ID_REG_ARM32_PC || dst2.getRegister().getId() == ID_REG_ARM32_PC)) {
            node = this->symbolicEngine->getOperandAst(inst, pc);
          } else {
            node = this->astCtxt->bv(inst.getNextAddress(), pc.getBitSize());
          }

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicRegisterExpression(inst, node, this->architecture->getParentRegister(ID_REG_ARM32_PC), "Program Counter");

          /* Spread taint */
          expr->isTainted = this->taintEngine->setTaintRegister(this->architecture->getParentRegister(ID_REG_ARM32_PC), triton::engines::taint::UNTAINTED);
        }


        triton::ast::SharedAbstractNode Arm32Semantics::getCodeConditionAst(triton::arch::Instruction& inst) {

          switch (inst.getCodeCondition()) {
            // Always. Any flags. This suffix is normally omitted.
            case triton::arch::arm::ID_CONDITION_AL: {
              return this->astCtxt->equal(this->astCtxt->bvtrue(), this->astCtxt->bvtrue());
            }

            // Equal. Z set.
            case triton::arch::arm::ID_CONDITION_EQ: {
              auto z = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_Z)));
              return this->astCtxt->equal(z, this->astCtxt->bvtrue());
            }

            // Signed >=. N and V the same.
            case triton::arch::arm::ID_CONDITION_GE: {
              auto n = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_N)));
              auto v = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_V)));
              return this->astCtxt->equal(n, v);
            }

            // Signed >. Z clear, N and V the same.
            case triton::arch::arm::ID_CONDITION_GT: {
              auto z = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_Z)));
              auto n = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_N)));
              auto v = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_V)));
              return this->astCtxt->land(
                        this->astCtxt->equal(z, this->astCtxt->bvfalse()),
                        this->astCtxt->equal(n, v)
                      );
            }

            // Higher (unsigned >). C set and Z clear.
            case triton::arch::arm::ID_CONDITION_HI: {
              auto c = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_C)));
              auto z = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_Z)));
              return this->astCtxt->land(
                        this->astCtxt->equal(c, this->astCtxt->bvtrue()),
                        this->astCtxt->equal(z, this->astCtxt->bvfalse())
                      );
            }

            // Higher or same (unsigned >=). C set.
            case triton::arch::arm::ID_CONDITION_HS: {
              auto c = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_C)));
              return this->astCtxt->equal(c, this->astCtxt->bvtrue());
            }

            // Signed <=. Z set or N and V differ.
            case triton::arch::arm::ID_CONDITION_LE: {
              auto z = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_Z)));
              auto n = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_N)));
              auto v = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_V)));
              return this->astCtxt->lor(
                        this->astCtxt->equal(z, this->astCtxt->bvtrue()),
                        this->astCtxt->lnot(this->astCtxt->equal(n, v))
                      );
            }

            // Lower (unsigned <). C clear.
            case triton::arch::arm::ID_CONDITION_LO: {
              auto c = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_C)));
              return this->astCtxt->equal(c, this->astCtxt->bvfalse());
            }

            // Lower or same (unsigned <=). C clear or Z set.
            case triton::arch::arm::ID_CONDITION_LS: {
              auto c = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_C)));
              auto z = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_Z)));
              return this->astCtxt->lor(
                        this->astCtxt->equal(c, this->astCtxt->bvfalse()),
                        this->astCtxt->equal(z, this->astCtxt->bvtrue())
                      );
            }

            // Signed <. N and V differ.
            case triton::arch::arm::ID_CONDITION_LT: {
              auto n = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_N)));
              auto v = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_V)));
              return this->astCtxt->lnot(this->astCtxt->equal(n, v));
            }

            // Negative. N set.
            case triton::arch::arm::ID_CONDITION_MI: {
              auto n = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_N)));
              return this->astCtxt->equal(n, this->astCtxt->bvtrue());
            }

            // Not equal. Z clear.
            case triton::arch::arm::ID_CONDITION_NE: {
              auto z = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_Z)));
              return this->astCtxt->equal(z, this->astCtxt->bvfalse());
            }

            // Positive or zero. N clear.
            case triton::arch::arm::ID_CONDITION_PL: {
              auto n = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_N)));
              return this->astCtxt->equal(n, this->astCtxt->bvfalse());
            }

            // No overflow. V clear.
            case triton::arch::arm::ID_CONDITION_VC: {
              auto v = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_V)));
              return this->astCtxt->equal(v, this->astCtxt->bvfalse());
            }

            // Overflow. V set.
            case triton::arch::arm::ID_CONDITION_VS: {
              auto v = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_V)));
              return this->astCtxt->equal(v, this->astCtxt->bvtrue());
            }

            default:
              /* The instruction don't use condition, so just return the 'true' node */
              return this->astCtxt->equal(this->astCtxt->bvtrue(), this->astCtxt->bvtrue());
          }
        }


        bool Arm32Semantics::getCodeConditionTaintState(const triton::arch::Instruction& inst) {
          switch (inst.getCodeCondition()) {
            // Always. Any flags. This suffix is normally omitted.
            case triton::arch::arm::ID_CONDITION_AL: {
              return false;
            }

            // Equal. Z set.
            // Not equal. Z clear.
            case triton::arch::arm::ID_CONDITION_EQ:
            case triton::arch::arm::ID_CONDITION_NE: {
              auto z = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_Z));
              return this->taintEngine->isTainted(z);
            }

            // Signed >=. N and V the same.
            // Signed <. N and V differ.
            case triton::arch::arm::ID_CONDITION_GE:
            case triton::arch::arm::ID_CONDITION_LT: {
              auto n = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_N));
              auto v = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_V));
              return this->taintEngine->isTainted(n) | this->taintEngine->isTainted(v);
            }

            // Signed >. Z clear, N and V the same.
            // Signed <=. Z set, N and V differ.
            case triton::arch::arm::ID_CONDITION_GT:
            case triton::arch::arm::ID_CONDITION_LE: {
              auto z = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_Z));
              auto n = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_N));
              auto v = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_V));
              return this->taintEngine->isTainted(z) | this->taintEngine->isTainted(n) | this->taintEngine->isTainted(v);
            }

            // Higher (unsigned >). C set and Z clear.
            // Lower or same (unsigned <=). C clear or Z set.
            case triton::arch::arm::ID_CONDITION_HI:
            case triton::arch::arm::ID_CONDITION_LS: {
              auto c = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_C));
              auto z = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_Z));
              return this->taintEngine->isTainted(c) | this->taintEngine->isTainted(z);
            }

            // Higher or same (unsigned >=). C set.
            // Lower (unsigned <). C clear.
            case triton::arch::arm::ID_CONDITION_HS:
            case triton::arch::arm::ID_CONDITION_LO: {
              auto c = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_C));
              return this->taintEngine->isTainted(c);
            }

            // Negative. N set.
            // Positive or zero. N clear.
            case triton::arch::arm::ID_CONDITION_MI:
            case triton::arch::arm::ID_CONDITION_PL: {
              auto n = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_N));
              return this->taintEngine->isTainted(n);
            }

            // No overflow. V clear.
            // Overflow. V set.
            case triton::arch::arm::ID_CONDITION_VC:
            case triton::arch::arm::ID_CONDITION_VS: {
              auto v = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_V));
              return this->taintEngine->isTainted(v);
            }

            default:
              return false;
          }
        }


        void Arm32Semantics::spreadTaint(triton::arch::Instruction& inst,
                                         const triton::ast::SharedAbstractNode& cond,
                                         const triton::engines::symbolic::SharedSymbolicExpression& expr,
                                         const triton::arch::OperandWrapper& operand,
                                         bool taint) {

          if (this->getCodeConditionTaintState(inst) == true) {
            expr->isTainted = this->taintEngine->setTaint(operand, true);
          }
          else if (cond->evaluate() == true) {
            expr->isTainted = this->taintEngine->setTaint(operand, taint);
            inst.setConditionTaken(true);
          }
          else {
            expr->isTainted = this->taintEngine->isTainted(operand);
          }
        }


        void Arm32Semantics::nf_s(triton::arch::Instruction& inst,
                                  const triton::ast::SharedAbstractNode& cond,
                                  const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                  triton::arch::OperandWrapper& dst) {

          auto nf   = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_N));
          auto high = dst.getHigh();

          /*
           * Create the semantic, considering conditional execution.
           * nf = MSB(result)
           */
          auto node1 = this->astCtxt->extract(high, high, this->astCtxt->reference(parent));
          auto node2 = this->symbolicEngine->getOperandAst(nf);
          auto node3 = this->astCtxt->ite(cond, node1, node2);

          /* Create the symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node3, nf, "Negative flag");

          /* Spread the taint from the parent to the child */
          this->spreadTaint(inst, cond, expr, nf, parent->isTainted);
        }


        void Arm32Semantics::zf_s(triton::arch::Instruction& inst,
                                  const triton::ast::SharedAbstractNode& cond,
                                  const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                  triton::arch::OperandWrapper& dst) {

          auto zf     = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_Z));
          auto bvSize = dst.getBitSize();
          auto low    = dst.getLow();
          auto high   = dst.getHigh();

          /*
           * Create the semantic, considering conditional execution.
           * zf = 0 == result
           */
          auto node1 = this->astCtxt->ite(
                        this->astCtxt->equal(
                          this->astCtxt->extract(high, low, this->astCtxt->reference(parent)),
                          this->astCtxt->bv(0, bvSize)
                        ),
                        this->astCtxt->bv(1, 1),
                        this->astCtxt->bv(0, 1)
                      );
          auto node2 = this->symbolicEngine->getOperandAst(zf);
          auto node3 = this->astCtxt->ite(cond, node1, node2);

          /* Create the symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node3, zf, "Zero flag");

          /* Spread the taint from the parent to the child */
          this->spreadTaint(inst, cond, expr, zf, parent->isTainted);
        }


        void Arm32Semantics::cfAdd_s(triton::arch::Instruction& inst,
                                     const triton::ast::SharedAbstractNode& cond,
                                     const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                     triton::arch::OperandWrapper& dst,
                                     triton::ast::SharedAbstractNode& op1,
                                     triton::ast::SharedAbstractNode& op2) {

          auto cf     = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_C));
          auto bvSize = dst.getBitSize();
          auto low    = dst.getLow();
          auto high   = dst.getHigh();

          /*
           * Create the semantic, considering conditional execution.
           * cf = MSB((op1 & op2) ^ ((op1 ^ op2 ^ result) & (op1 ^ op2)));
           */
          auto node1 = this->astCtxt->extract(bvSize-1, bvSize-1,
                        this->astCtxt->bvxor(
                          this->astCtxt->bvand(op1, op2),
                          this->astCtxt->bvand(
                            this->astCtxt->bvxor(
                              this->astCtxt->bvxor(op1, op2),
                              this->astCtxt->extract(high, low, this->astCtxt->reference(parent))
                            ),
                          this->astCtxt->bvxor(op1, op2))
                        )
                      );
          auto node2 = this->symbolicEngine->getOperandAst(cf);
          auto node3 = this->astCtxt->ite(cond, node1, node2);

          /* Create the symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node3, cf, "Carry flag");

          /* Spread the taint from the parent to the child */
          this->spreadTaint(inst, cond, expr, cf, parent->isTainted);
        }


        void Arm32Semantics::cfSub_s(triton::arch::Instruction& inst,
                                     const triton::ast::SharedAbstractNode& cond,
                                     const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                     triton::arch::OperandWrapper& dst,
                                     triton::ast::SharedAbstractNode& op1,
                                     triton::ast::SharedAbstractNode& op2) {

          auto cf     = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_C));
          auto bvSize = dst.getBitSize();
          auto low    = dst.getLow();
          auto high   = dst.getHigh();

          /*
           * Create the semantic.
           * cf = (MSB(((op1 ^ op2 ^ result) ^ ((op1 ^ result) & (op1 ^ op2))))) ^ 1
           */
          auto node1 = this->astCtxt->bvxor(
                        this->astCtxt->extract(bvSize-1, bvSize-1,
                          this->astCtxt->bvxor(
                            this->astCtxt->bvxor(op1, this->astCtxt->bvxor(op2, this->astCtxt->extract(high, low, this->astCtxt->reference(parent)))),
                            this->astCtxt->bvand(
                              this->astCtxt->bvxor(op1, this->astCtxt->extract(high, low, this->astCtxt->reference(parent))),
                              this->astCtxt->bvxor(op1, op2)
                            )
                          )
                        ),
                        this->astCtxt->bvtrue()
                      );
          auto node2 = this->symbolicEngine->getOperandAst(cf);
          auto node3 = this->astCtxt->ite(cond, node1, node2);

          /* Create the symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node3, cf, "Carry flag");

          /* Spread the taint from the parent to the child */
          this->spreadTaint(inst, cond, expr, cf, parent->isTainted);
        }


        void Arm32Semantics::nfSmull_s(triton::arch::Instruction& inst,
                                       const triton::ast::SharedAbstractNode& cond,
                                       const triton::engines::symbolic::SharedSymbolicExpression& parent1,
                                       const triton::engines::symbolic::SharedSymbolicExpression& parent2,
                                       triton::arch::OperandWrapper& dst1,
                                       triton::arch::OperandWrapper& dst2) {

          auto nf   = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_N));
          auto high = dst2.getHigh();

          /*
           * Create the semantic, considering conditional execution.
           * nf = MSB(result)
           */
          auto node1 = this->astCtxt->extract(high, high, this->astCtxt->reference(parent2));
          auto node2 = this->symbolicEngine->getOperandAst(nf);
          auto node3 = this->astCtxt->ite(cond, node1, node2);

          /* Create the symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node3, nf, "Negative flag");

          /* Spread the taint from the parent to the child */
          this->spreadTaint(inst, cond, expr, nf, parent1->isTainted | parent2->isTainted);
        }


        void Arm32Semantics::zfSmull_s(triton::arch::Instruction& inst,
                                       const triton::ast::SharedAbstractNode& cond,
                                       const triton::engines::symbolic::SharedSymbolicExpression& parent1,
                                       const triton::engines::symbolic::SharedSymbolicExpression& parent2,
                                       triton::arch::OperandWrapper& dst1,
                                       triton::arch::OperandWrapper& dst2) {

          auto zf     = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_Z));
          auto bvSize = dst1.getBitSize();
          auto low    = dst1.getLow();
          auto high   = dst1.getHigh();

          /*
           * Create the semantic, considering conditional execution.
           * zf = 0 == result
           */
          auto node1 = this->astCtxt->ite(
                        this->astCtxt->land(
                          this->astCtxt->equal(
                            this->astCtxt->extract(high, low, this->astCtxt->reference(parent1)),
                            this->astCtxt->bv(0, bvSize)
                          ),
                          this->astCtxt->equal(
                            this->astCtxt->extract(high, low, this->astCtxt->reference(parent2)),
                            this->astCtxt->bv(0, bvSize)
                          )
                        ),
                        this->astCtxt->bv(1, 1),
                        this->astCtxt->bv(0, 1)
                      );
          auto node2 = this->symbolicEngine->getOperandAst(zf);
          auto node3 = this->astCtxt->ite(cond, node1, node2);

          /* Create the symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node3, zf, "Zero flag");

          /* Spread the taint from the parent to the child */
          this->spreadTaint(inst, cond, expr, zf, parent1->isTainted | parent2->isTainted);
        }


        void Arm32Semantics::vfAdd_s(triton::arch::Instruction& inst,
                                     const triton::ast::SharedAbstractNode& cond,
                                     const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                     triton::arch::OperandWrapper& dst,
                                     triton::ast::SharedAbstractNode& op1,
                                     triton::ast::SharedAbstractNode& op2) {

          auto vf     = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_V));
          auto bvSize = dst.getBitSize();
          auto low    = dst.getLow();
          auto high   = dst.getHigh();

          /*
           * Create the semantic, considering conditional execution.
           * vf = MSB((op1 ^ ~op2) & (op1 ^ result))
           */
          auto node1 = this->astCtxt->extract(bvSize-1, bvSize-1,
                        this->astCtxt->bvand(
                          this->astCtxt->bvxor(op1, this->astCtxt->bvnot(op2)),
                          this->astCtxt->bvxor(op1, this->astCtxt->extract(high, low, this->astCtxt->reference(parent)))
                        )
                      );
          auto node2 = this->symbolicEngine->getOperandAst(vf);
          auto node3 = this->astCtxt->ite(cond, node1, node2);

          /* Create the symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node3, vf, "Overflow flag");

          /* Spread the taint from the parent to the child */
          this->spreadTaint(inst, cond, expr, vf, parent->isTainted);
        }


        void Arm32Semantics::vfSub_s(triton::arch::Instruction& inst,
                                     const triton::ast::SharedAbstractNode& cond,
                                     const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                     triton::arch::OperandWrapper& dst,
                                     triton::ast::SharedAbstractNode& op1,
                                     triton::ast::SharedAbstractNode& op2) {

          auto vf     = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_V));
          auto bvSize = dst.getBitSize();
          auto low    = dst.getLow();
          auto high   = dst.getHigh();

          /*
           * Create the semantic.
           * vf = MSB((op1 ^ op2) & (op1 ^ result))
           */
          auto node1 = this->astCtxt->extract(bvSize-1, bvSize-1,
                        this->astCtxt->bvand(
                          this->astCtxt->bvxor(op1, op2),
                          this->astCtxt->bvxor(op1, this->astCtxt->extract(high, low, this->astCtxt->reference(parent)))
                        )
                      );
          auto node2 = this->symbolicEngine->getOperandAst(vf);
          auto node3 = this->astCtxt->ite(cond, node1, node2);

          /* Create the symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node3, vf, "Overflow flag");

          /* Spread the taint from the parent to the child */
          this->spreadTaint(inst, cond, expr, vf, parent->isTainted);
        }


        void Arm32Semantics::adc_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];
          auto& src2 = inst.operands[2];
          auto  cf   = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_C));

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);
          auto op2 = this->getArm32SourceOperandAst(inst, src2);
          auto op3 = this->getArm32SourceOperandAst(inst, cf);

          /* Create the semantics */
          auto node1 = this->astCtxt->bvadd(
                          this->astCtxt->bvadd(op1, op2),
                          this->astCtxt->zx(dst.getBitSize()-1, op3)
                        );
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "ADC(S) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(cf));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->cfAdd_s(inst, cond, expr, dst, op1, op2);
            this->nf_s(inst, cond, expr, dst);
            this->vfAdd_s(inst, cond, expr, dst, op1, op2);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node1);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::add_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];
          auto& src2 = inst.operands[2];

          /* Process modified immediate constants (expand immediate) */
          /* For more information, look for "Modified immediate constants in ARM
           * instructions" in the reference manual. For example:
           * "adc ip, ip, #16, #20".
           */
          if (inst.operands.size() == 4) {
            auto src3 = inst.operands[3];

            if (src2.getType() == OP_IMM && src3.getType() == OP_IMM) {
              auto size  = src2.getSize();
              auto value = src2.getImmediate().getValue();
              auto shift = src3.getImmediate().getValue();

              /* Replace src2 with the expanded immediate */
              src2 = triton::arch::OperandWrapper(triton::arch::Immediate(this->ror(value, shift), size));
            } else {
              throw triton::exceptions::Semantics("Arm32Semantics::add_s(): Invalid operand type.");
            }
          }

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);
          auto op2 = this->getArm32SourceOperandAst(inst, src2);

          /* Create the semantics */
          auto node1 = this->astCtxt->bvadd(op1, op2);
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "ADD(S) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->cfAdd_s(inst, cond, expr, dst, op1, op2);
            this->nf_s(inst, cond, expr, dst);
            this->vfAdd_s(inst, cond, expr, dst, op1, op2);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node1);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::and_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];
          auto& src2 = inst.operands[2];

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);
          auto op2 = this->getArm32SourceOperandAst(inst, src2);

          /* Create the semantics */
          auto node1 = this->astCtxt->bvand(op1, op2);
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "AND(S) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->cfBitwise_s(inst, cond, expr, src2);
            this->nf_s(inst, cond, expr, dst);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node1);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::asr_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];

          /* Create symbolic operands */
          auto op1base = this->getArm32SourceBaseOperandAst(inst, src1);
          auto op1     = this->getArm32SourceOperandAst(inst, src1);

          /* Create the semantics */
          triton::ast::SharedAbstractNode node1;

          /* Two-operand version: ASR {<Rd>,} <Rm>, #<imm>. Here #<imm> is
           * interpreted as a shift value for <Rm>, which is handled directly
           * by the getArm32SourceOperandAst function. */
          if (inst.operands.size() == 2) {
            node1 = op1;
          }
          /* Three-operand version: ASR {<Rd>,} <Rn>, <Rm>. Here <Rm> is a
           * regular register and holds the value to shift the <Rn> register.
           * The operation must be explicitly done here.
           */
          else {
            auto& src2 = inst.operands[2];

            auto op2 = this->getArm32SourceOperandAst(inst, src2);

            node1 = this->astCtxt->bvashr(
                      op1,
                      this->astCtxt->zx(
                        DWORD_SIZE_BIT-8,
                        this->astCtxt->extract(7, 0, op2)
                      )
                    );
          }

          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "ASR(S) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          auto taint = this->taintEngine->isTainted(src1);

          if (inst.operands.size() == 3) {
            auto& src2 = inst.operands[2];

            taint |= this->taintEngine->isTainted(src2);
          }

          this->spreadTaint(inst, cond, expr, dst, taint);

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            auto& src = inst.operands.size() == 2 ? inst.operands[1] : inst.operands[2];

            this->cfAsr_s(inst, cond, expr, op1base, src);
            this->nf_s(inst, cond, expr, dst);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node2);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::b_s(triton::arch::Instruction& inst) {
          auto  dst = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_PC));
          auto& src = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src);
          auto op2 = this->astCtxt->bv(inst.getNextAddress(), dst.getBitSize());

          /* Create the semantics */
          auto cond   = this->getCodeConditionAst(inst);
          auto pcNode = this->astCtxt->ite(cond, op1, op2);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, pcNode, dst, "B operation - Program Counter");

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->getCodeConditionTaintState(inst));

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Create the path constraint */
          this->symbolicEngine->pushPathConstraint(inst, expr);
        }


        void Arm32Semantics::bic_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];
          auto& src2 = inst.operands[2];

          /* Create symbolic operands */
          auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
          auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

          /* Create the semantics */
          auto node1 = this->astCtxt->bvand(op1, this->astCtxt->bvnot(op2));
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "BIC(S) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->cfBitwise_s(inst, cond, expr, src2);
            this->nf_s(inst, cond, expr, dst);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node1);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::bl_s(triton::arch::Instruction& inst, bool exchange) {
          auto  dst1 = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_R14));
          auto  dst2 = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_PC));
          auto& src  = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src);
          auto op2 = this->symbolicEngine->getOperandAst(inst, dst1);
          auto op3 = this->symbolicEngine->getOperandAst(inst, dst2);
          auto op4 = this->astCtxt->bv(inst.getNextAddress(), dst2.getBitSize());

          /* Create the semantics */
          auto cond = this->getCodeConditionAst(inst);

          /* Create semantics for the Link register */
          /* If the condition holds, the value of LR is equal to PC plus the
           * size of the current instruction (i.e. the address of the next
           * instruction). Additionally, the instruction set selection bit
           * (LSB) is set accordindly. If the condition does not hold, the value
           * of LR remains the same.
           */
          auto instSize = this->astCtxt->bv(inst.getSize(), dst2.getBitSize());
          auto lrNode   = this->astCtxt->ite(cond, this->adjustISSB(this->astCtxt->bvadd(op3, instSize)), op2);

          /* Create semantics for the Program Counter register */
          /* If the conditions holds, the value of PC is equal to the operand
           * of the instruction. Also, clear the instruction set selection bit
           * (LSB). If the condition does not hold, the value of PC is equal to
           * the next instruction.
           */
          auto pcNode = this->astCtxt->ite(cond, this->clearISSB(op1), op4);

          /* Create symbolic expression */
          auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, lrNode, dst1, "BL(X) operation - Link Register");
          auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, pcNode, dst2, "BL(X) operation - Program Counter");

          /* Spread taint */
          this->spreadTaint(inst, cond, expr1, dst1, this->getCodeConditionTaintState(inst));
          this->spreadTaint(inst, cond, expr2, dst2, this->getCodeConditionTaintState(inst));

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            if (exchange) {
              this->exchangeInstructionSet(src, op1);
            }
          }

          /* Create the path constraint */
          this->symbolicEngine->pushPathConstraint(inst, expr2);
        }


        void Arm32Semantics::bx_s(triton::arch::Instruction& inst) {
          auto  dst = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_PC));
          auto& src = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src);
          auto op2 = this->astCtxt->bv(inst.getNextAddress(), dst.getBitSize());

          /* Create the semantics */
          auto cond = this->getCodeConditionAst(inst);

          /* If the conditions holds, the value of PC is equal to the operand
           * of the instruction. Also, clear the instruction set selection bit
           * (LSB). If the condition does not hold, the value of PC is equal to
           * the next instruction.
           */
          auto node = this->astCtxt->ite(cond, this->clearISSB(op1), op2);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "BX operation - Program Counter");

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->getCodeConditionTaintState(inst));

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            this->exchangeInstructionSet(src, op1);
          }

          /* Create the path constraint */
          this->symbolicEngine->pushPathConstraint(inst, expr);
        }


        void Arm32Semantics::cbz_s(triton::arch::Instruction& inst) {
          auto  dst  = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_PC));
          auto& src1 = inst.operands[0];
          auto& src2 = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);
          auto op2 = this->getArm32SourceOperandAst(inst, src2);
          auto op3 = this->astCtxt->bv(inst.getNextAddress(), dst.getBitSize());

          /* Create the semantics */
          auto pcNode = this->astCtxt->ite(
                          this->astCtxt->equal(
                            op1,
                            this->astCtxt->bv(0, op1->getBitvectorSize())
                          ),
                          op2,
                          op3
                        );

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, pcNode, dst, "CBZ operation - Program Counter");

          /* Spread taint */
          expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

          /* Set condition flag */
          if (op1->evaluate() == 0) {
            inst.setConditionTaken(true);
          }

          /* Create the path constraint */
          this->symbolicEngine->pushPathConstraint(inst, expr);
        }


        void Arm32Semantics::clz_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  bvSize = dst.getBitSize();

          /* Create symbolic operands */
          auto op = this->getArm32SourceOperandAst(inst, src);

          /* Create the semantics */
          auto node1 = this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(31, 31, op), this->astCtxt->bvtrue()), this->astCtxt->bv(0, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(30, 30, op), this->astCtxt->bvtrue()), this->astCtxt->bv(1, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(29, 29, op), this->astCtxt->bvtrue()), this->astCtxt->bv(2, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(28, 28, op), this->astCtxt->bvtrue()), this->astCtxt->bv(3, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(27, 27, op), this->astCtxt->bvtrue()), this->astCtxt->bv(4, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(26, 26, op), this->astCtxt->bvtrue()), this->astCtxt->bv(5, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(25, 25, op), this->astCtxt->bvtrue()), this->astCtxt->bv(6, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(24, 24, op), this->astCtxt->bvtrue()), this->astCtxt->bv(7, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(23, 23, op), this->astCtxt->bvtrue()), this->astCtxt->bv(8, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(22, 22, op), this->astCtxt->bvtrue()), this->astCtxt->bv(9, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(21, 21, op), this->astCtxt->bvtrue()), this->astCtxt->bv(10, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(20, 20, op), this->astCtxt->bvtrue()), this->astCtxt->bv(11, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(19, 19, op), this->astCtxt->bvtrue()), this->astCtxt->bv(12, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(18, 18, op), this->astCtxt->bvtrue()), this->astCtxt->bv(13, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(17, 17, op), this->astCtxt->bvtrue()), this->astCtxt->bv(14, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(16, 16, op), this->astCtxt->bvtrue()), this->astCtxt->bv(15, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(15, 15, op), this->astCtxt->bvtrue()), this->astCtxt->bv(16, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(14, 14, op), this->astCtxt->bvtrue()), this->astCtxt->bv(17, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(13, 13, op), this->astCtxt->bvtrue()), this->astCtxt->bv(18, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(12, 12, op), this->astCtxt->bvtrue()), this->astCtxt->bv(19, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(11, 11, op), this->astCtxt->bvtrue()), this->astCtxt->bv(20, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(10, 10, op), this->astCtxt->bvtrue()), this->astCtxt->bv(21, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(9, 9, op), this->astCtxt->bvtrue()),   this->astCtxt->bv(22, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(8, 8, op), this->astCtxt->bvtrue()),   this->astCtxt->bv(23, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(7, 7, op), this->astCtxt->bvtrue()),   this->astCtxt->bv(24, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(6, 6, op), this->astCtxt->bvtrue()),   this->astCtxt->bv(25, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(5, 5, op), this->astCtxt->bvtrue()),   this->astCtxt->bv(26, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(4, 4, op), this->astCtxt->bvtrue()),   this->astCtxt->bv(27, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(3, 3, op), this->astCtxt->bvtrue()),   this->astCtxt->bv(28, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(2, 2, op), this->astCtxt->bvtrue()),   this->astCtxt->bv(29, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(1, 1, op), this->astCtxt->bvtrue()),   this->astCtxt->bv(30, bvSize),
                       this->astCtxt->ite(this->astCtxt->equal(this->astCtxt->extract(0, 0, op), this->astCtxt->bvtrue()),   this->astCtxt->bv(31, bvSize),
                       this->astCtxt->bv(32, bvSize)
                       ))))))))))))))))))))))))))))))));
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "CLZ operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src));

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::cmp_s(triton::arch::Instruction& inst) {
          auto& src1 = inst.operands[0];
          auto& src2 = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);
          auto op2 = this->getArm32SourceOperandAst(inst, src2);

          /* Create the semantics */
          auto cond = this->getCodeConditionAst(inst);
          auto node1 = this->astCtxt->bvsub(op1, op2);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "CMP operation");

          /* Update symbolic flags */
          this->cfSub_s(inst, cond, expr, src1, op1, op2);
          this->nf_s(inst, cond, expr, src1);
          this->vfSub_s(inst, cond, expr, src1, op1, op2);
          this->zf_s(inst, cond, expr, src1);

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst);
        }


        void Arm32Semantics::eor_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];
          auto& src2 = inst.operands[2];

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);
          auto op2 = this->getArm32SourceOperandAst(inst, src2);

          /* Create the semantics */
          auto node1 = this->astCtxt->bvxor(op1, op2);
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "EOR(S) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->cfBitwise_s(inst, cond, expr, src2);
            this->nf_s(inst, cond, expr, dst);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node1);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::ldm_s(triton::arch::Instruction& inst) {
          auto& base          = inst.operands[0];
          triton::uint32 size = DWORD_SIZE;

          /* Create symbolic operands */
          auto baseNode = this->symbolicEngine->getOperandAst(inst, base);

          /* Create the semantics */
          auto cond  = this->getCodeConditionAst(inst);

          bool updateControlFlow = true;

          for (unsigned int i = 1; i < inst.operands.size(); i++) {
            auto& dst = inst.operands[i];

            /* Compute memory address */
            auto addr = baseNode->evaluate().convert_to<triton::uint64>() + size * (i-1);
            auto src  = triton::arch::OperandWrapper(triton::arch::MemoryAccess(addr, size));

            /* Create symbolic operands */
            auto op2 = this->getArm32SourceOperandAst(inst, src);
            auto op3 = this->getArm32SourceOperandAst(inst, dst);

            /* Create the semantics */
            auto node1 = op2;

            /* In case PC is one of the destination registers, clear ISSB
             * (instruction set selection bit) from the value that will be
             * assigned to it.
             */
            if (dst.getRegister().getId() == ID_REG_ARM32_PC) {
              node1 = this->clearISSB(op2);
            }

            auto node2 = this->astCtxt->ite(cond, node1, op3);

            /* Create symbolic expression */
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "LDM operation - LOAD access");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr1, dst, this->taintEngine->isTainted(base) | this->taintEngine->isTainted(src));

            /* If PC was modified, do not update the control flow at the end of
             * the function.
             */
            if (cond->evaluate() == true && dst.getRegister().getId() == ID_REG_ARM32_PC) {
              updateControlFlow = false;

              /* Update swtich mode accordingly. */
              this->updateExecutionState(dst, op2);
            }
          }

          if (inst.isWriteBack() == true) {
            /* Create the semantics of the base register */
            auto node1 = this->astCtxt->ite(
                            cond,
                            this->astCtxt->bvadd(
                              baseNode,
                              this->astCtxt->bv((inst.operands.size() - 1) * size, base.getBitSize())
                            ),
                            baseNode
                          );

            /* Create symbolic expression */
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node1, base, "LDM operation - Base register computation");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr2, base, this->taintEngine->isTainted(base));
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Update the symbolic control flow */
          if (updateControlFlow) {
            this->controlFlow_s(inst);
          }
        }


        void Arm32Semantics::ldr_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op = this->getArm32SourceOperandAst(inst, src);

          /* Create the semantics */
          auto node1 = this->buildConditionalSemantics(inst, dst, op);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "LDR operation - LOAD access");

          /* Get condition code node */
          auto cond = node1->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src));

          /* TODO: Add Offset addressing. */
          /* Optional behavior. Post-indexed computation of the base register */
          /* LDR <Rt>, [<Rn>], #+/-<imm> */
          if (inst.operands.size() == 3) {
            auto& imm  = inst.operands[2].getImmediate();
            auto& base = src.getMemory().getBaseRegister();

            /* Create symbolic operands of the post computation */
            auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
            auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

            /* Create the semantics of the base register */
            auto thenNode = this->astCtxt->bvadd(baseNode, this->astCtxt->sx(base.getBitSize() - imm.getBitSize(), immNode));

            if (imm.getSubtracted() == true) {
              thenNode = this->astCtxt->bvsub(baseNode, this->astCtxt->sx(base.getBitSize() - imm.getBitSize(), immNode));
            }

            auto node2 = this->astCtxt->ite(cond, thenNode, baseNode);

            /* Create symbolic expression */
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "LDR operation - Post-indexed base register computation");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr2, base, this->taintEngine->isTainted(base));
          }

          /* Optional behavior. Pre-indexed computation of the base register */
          /* LDR <Rt>, [<Rn>, #+/-<imm>]! */
          else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
            auto& base = src.getMemory().getBaseRegister();

            /* Create symbolic operands of the post computation */
            auto baseNode = this->symbolicEngine->getOperandAst(inst, base);

            /* Create the semantics of the base register */
            auto node3 = this->astCtxt->ite(cond, src.getMemory().getLeaAst(), baseNode);

            /* Create symbolic expression */
            auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "LDR operation - Pre-indexed base register computation");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr3, base, this->taintEngine->isTainted(base));
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node1);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::ldrb_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Special behavior: Define that the size of the memory access is 8 bits */
          src.getMemory().setPair(std::make_pair(7, 0));

          /* Create symbolic operands */
          auto op = this->symbolicEngine->getOperandAst(inst, src);

          /* Create the semantics */
          auto node1 = this->astCtxt->zx(dst.getBitSize() - src.getBitSize(), op);
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "LDRB operation - LOAD access");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src));

          /* TODO: Add Offset addressing. */
          /* Optional behavior. Post-indexed computation of the base register */
          /* LDR <Rt>, [<Rn>], #+/-<imm> */
          if (inst.operands.size() == 3) {
            auto& imm  = inst.operands[2].getImmediate();
            auto& base = src.getMemory().getBaseRegister();

            /* Create symbolic operands of the post computation */
            auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
            auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

            /* Create the semantics of the base register */
            auto node2 = this->astCtxt->ite(
                            cond,
                            this->astCtxt->bvadd(baseNode, this->astCtxt->sx(base.getBitSize() - imm.getBitSize(), immNode)),
                            baseNode
                          );

            /* Create symbolic expression */
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "LDRB operation - Post-indexed base register computation");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr2, base, this->taintEngine->isTainted(base));
          }

          /* Optional behavior. Pre-indexed computation of the base register */
          /* LDR <Rt>, [<Rn>, #+/-<imm>]! */
          else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
            auto& base = src.getMemory().getBaseRegister();

            /* Create symbolic operands of the post computation */
            auto baseNode = this->symbolicEngine->getOperandAst(inst, base);

            /* Create the semantics of the base register */
            auto node3 = this->astCtxt->ite(cond, src.getMemory().getLeaAst(), baseNode);

            /* Create symbolic expression */
            auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "LDRB operation - Pre-indexed base register computation");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr3, base, this->taintEngine->isTainted(base));
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node1);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::ldrd_s(triton::arch::Instruction& inst) {
          auto& base          = inst.operands[2];
          triton::uint32 size = DWORD_SIZE;

          /* Create the semantics */
          auto cond  = this->getCodeConditionAst(inst);

          for (unsigned int i = 0; i < 2; i++) {
            auto& dst = inst.operands[i];

            /* Compute memory address */
            auto addr = base.getMemory().getAddress() + size * i;
            auto src  = triton::arch::OperandWrapper(triton::arch::MemoryAccess(addr, size));

            /* Create symbolic operands */
            auto op2 = this->getArm32SourceOperandAst(inst, src);
            auto op3 = this->getArm32SourceOperandAst(inst, dst);

            /* Create the semantics */
            auto node = this->astCtxt->ite(cond, op2, op3);

            /* Create symbolic expression */
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDRD operation - LOAD access");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr1, dst, this->taintEngine->isTainted(base) | this->taintEngine->isTainted(src));
          }

          /* Optional behavior. Post-indexed computation of the base register */
          /* LDRD <Rt>, [<Rn>], #+/-<imm> */
          if (inst.operands.size() == 4) {
            auto& imm  = inst.operands[3].getImmediate();
            auto& base = inst.operands[2].getMemory().getBaseRegister();

            /* Create symbolic operands of the post computation */
            auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
            auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

            /* Create the semantics of the base register */
            auto node2 = this->astCtxt->ite(
                            cond,
                            this->astCtxt->bvadd(baseNode, this->astCtxt->sx(base.getBitSize() - imm.getBitSize(), immNode)),
                            baseNode
                          );

            /* Create symbolic expression */
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "LDRD operation - Post-indexed base register computation");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr2, base, this->taintEngine->isTainted(base));
          }

          /* Optional behavior. Pre-indexed computation of the base register */
          /* LDRD <Rt>, [<Rn>, #+/-<imm>]! */
          else if (inst.operands.size() == 3 && inst.isWriteBack() == true) {
            auto& base = inst.operands[2].getMemory().getBaseRegister();

            /* Create symbolic operands of the post computation */
            auto baseNode = this->symbolicEngine->getOperandAst(inst, base);

            /* Create the semantics of the base register */
            auto node3 = this->astCtxt->ite(cond, inst.operands[2].getMemory().getLeaAst(), baseNode);

            /* Create symbolic expression */
            auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "LDRD operation - Pre-indexed base register computation");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr3, base, this->taintEngine->isTainted(base));
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            /* TODO (cnheitman): There could be a execution mode switch. Fix. */
          }

          /* Update the symbolic control flow */
          /* TODO (cnheitman): Fix. (Similar to SMULL). */
          // this->controlFlow_s(inst, cond, dst1, dst2);
          this->controlFlow_s(inst);
        }


        void Arm32Semantics::lsl_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];

          /* Create symbolic operands */
          auto op1base = this->getArm32SourceBaseOperandAst(inst, src1);
          auto op1     = this->getArm32SourceOperandAst(inst, src1);

          /* Create the semantics */
          triton::ast::SharedAbstractNode node1;

          /* Two-operand version: LSL {<Rd>,} <Rm>, #<imm>. Here #<imm> is
           * interpreted as a shift value for <Rm>, which is handled directly
           * by the getArm32SourceOperandAst function. */
          if (inst.operands.size() == 2) {
            node1 = op1;
          }
          /* Three-operand version: LSL {<Rd>,} <Rn>, <Rm>. Here <Rm> is a
           * regular register and holds the value to shift the <Rn> register.
           * The operation must be explicitly done here.
           */
          else {
            auto& src2 = inst.operands[2];

            auto op2 = this->getArm32SourceOperandAst(inst, src2);

            node1 = this->astCtxt->bvshl(
                      op1,
                      this->astCtxt->zx(
                        DWORD_SIZE_BIT-8,
                        this->astCtxt->extract(7, 0, op2)
                      )
                    );
          }

          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "LSL(S) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          auto taint = this->taintEngine->isTainted(src1);

          if (inst.operands.size() == 3) {
            auto& src2 = inst.operands[2];

            taint |= this->taintEngine->isTainted(src2);
          }

          this->spreadTaint(inst, cond, expr, dst, taint);

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            auto& src = inst.operands.size() == 2 ? inst.operands[1] : inst.operands[2];

            this->cfLsl_s(inst, cond, expr, op1base, src);
            this->nf_s(inst, cond, expr, dst);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node2);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::lsr_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];

          /* Create symbolic operands */
          auto op1base = this->getArm32SourceBaseOperandAst(inst, src1);
          auto op1     = this->getArm32SourceOperandAst(inst, src1);

          /* Create the semantics */
          triton::ast::SharedAbstractNode node1;

          /* Two-operand version: ASR {<Rd>,} <Rm>, #<imm>. Here #<imm> is
           * interpreted as a shift value for <Rm>, which is handled directly
           * by the getArm32SourceOperandAst function. */
          if (inst.operands.size() == 2) {
            node1 = op1;
          }
          /* Three-operand version: ASR {<Rd>,} <Rn>, <Rm>. Here <Rm> is a
           * regular register and holds the value to shift the <Rn> register.
           * The operation must be explicitly done here.
           */
          else {
            auto& src2 = inst.operands[2];

            auto op2 = this->getArm32SourceOperandAst(inst, src2);

            node1 = this->astCtxt->bvlshr(
                      op1,
                      this->astCtxt->zx(
                        DWORD_SIZE_BIT-8,
                        this->astCtxt->extract(7, 0, op2)
                      )
                    );
          }

          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "LSR(S) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          auto taint = this->taintEngine->isTainted(src1);

          if (inst.operands.size() == 3) {
            auto& src2 = inst.operands[2];

            taint |= this->taintEngine->isTainted(src2);
          }

          this->spreadTaint(inst, cond, expr, dst, taint);

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            auto& src = inst.operands.size() == 2 ? inst.operands[1] : inst.operands[2];

            this->cfLsr_s(inst, cond, expr, op1base, src);
            this->nf_s(inst, cond, expr, dst);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node2);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::mov_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node1 = this->getArm32SourceOperandAst(inst, src);
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "MOV(s) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->nf_s(inst, cond, expr, dst);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node1);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::mul_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src1   = inst.operands[1];
          auto& src2   = inst.operands[2];
          auto  bvSize = dst.getBitSize();

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);
          auto op2 = this->getArm32SourceOperandAst(inst, src2);

          /* Create the semantics */
          auto mul   = this->astCtxt->bvmul(
                          this->astCtxt->sx(2*bvSize, op1),
                          this->astCtxt->sx(2*bvSize, op2)
                        );
          auto lower = this->astCtxt->extract(bvSize-1, 0, mul);
          auto node1 = this->buildConditionalSemantics(inst, dst, lower);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "MUL(S) operation");

          /* Get condition code node */
          auto cond = node1->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->nf_s(inst, cond, expr, dst);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::mvn_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op = this->getArm32SourceOperandAst(inst, src);

          /* Create the semantics */
          auto node1 = this->astCtxt->bvnot(op);
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "MVN(S) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->cfBitwise_s(inst, cond, expr, src);
            this->nf_s(inst, cond, expr, dst);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node1);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::orr_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];
          auto& src2 = inst.operands[2];

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);
          auto op2 = this->getArm32SourceOperandAst(inst, src2);

          /* Create the semantics */
          auto node1 = this->astCtxt->bvor(op1, op2);
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "OOR(S) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->cfBitwise_s(inst, cond, expr, src2);
            this->nf_s(inst, cond, expr, dst);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node1);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::pop_s(triton::arch::Instruction& inst) {
          auto stack          = this->architecture->getStackPointer();
          triton::uint32 size = stack.getSize();

          /* Create the semantics */
          auto cond  = this->getCodeConditionAst(inst);

          bool updateControlFlow = true;

          for (uint8_t i = 0; i < inst.operands.size(); i++) {
            auto& dst        = inst.operands[i];
            auto  stack      = this->architecture->getStackPointer();
            auto  stackValue = this->architecture->getConcreteRegisterValue(stack).convert_to<triton::uint64>();
            auto  src        = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue, size));

            /* Create symbolic operands */
            auto op1 = this->getArm32SourceOperandAst(inst, dst);
            auto op2 = this->getArm32SourceOperandAst(inst, src);

            /* Create the semantics */
            auto node1 = op2;

            /* In case PC is one of the destination registers, clear ISSB
             * (instruction set selection bit) from the value that will be
             * assigned to it.
             */
            if (dst.getRegister().getId() == ID_REG_ARM32_PC) {
              node1 = this->clearISSB(op2);
            }

            auto node2 = this->astCtxt->ite(cond, node1, op1);

            /* Create symbolic expression */
            auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "POP operation - Pop register");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src));

            /* Align stack */
            alignAddStack_s(inst, cond, size);

            /* If PC was modified, do not update the control flow at the end of
             * the function.
             */
            if (cond->evaluate() == true && dst.getRegister().getId() == ID_REG_ARM32_PC) {
              updateControlFlow = false;

              /* Update swtich mode accordingly. */
              this->updateExecutionState(dst, op2);
            }
          }

          /* Update the symbolic control flow */
          if (updateControlFlow) {
            this->controlFlow_s(inst);
          }
        }


        void Arm32Semantics::push_s(triton::arch::Instruction& inst) {
          auto stack          = this->architecture->getStackPointer();
          triton::uint32 size = stack.getSize();

          /* Create the semantics */
          auto cond = this->getCodeConditionAst(inst);

          for (int i = inst.operands.size()-1; i >= 0; i--) {
            auto& src = inst.operands[i];

            /* Create symbolic operands */
            auto op = this->getArm32SourceOperandAst(inst, src);

            /* Create the semantics - side effect */
            auto stackValue = alignSubStack_s(inst, cond, size);
            auto dst        = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue, size));

            /* Create the semantics */
            auto node = this->astCtxt->ite(cond, op, this->astCtxt->bv(stackValue, op->getBitvectorSize()));

            /* Create symbolic expression */
            auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PUSH operation - Push register");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src));
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst);
        }


        void Arm32Semantics::rev_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op = this->getArm32SourceOperandAst(inst, src);

          /* Create the semantics */
          std::list<triton::ast::SharedAbstractNode> bits;

          bits.push_front(this->astCtxt->extract(31, 24, op));
          bits.push_front(this->astCtxt->extract(23, 16, op));
          bits.push_front(this->astCtxt->extract(15, 8,  op));
          bits.push_front(this->astCtxt->extract(7,  0,  op));

          auto node1 = this->astCtxt->concat(bits);
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "REV operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src));

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node1);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::ror_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];

          /* Create symbolic operands */
          auto op1base = this->getArm32SourceBaseOperandAst(inst, src1);
          auto op1 = this->getArm32SourceOperandAst(inst, src1);

          /* Create the semantics */
          triton::ast::SharedAbstractNode node1;

          /* Two-operand version: ASR {<Rd>,} <Rm>, #<imm>. Here #<imm> is
           * interpreted as a shift value for <Rm>, which is handled directly
           * by the getArm32SourceOperandAst function. */
          if (inst.operands.size() == 2) {
            node1 = op1;
          }
          /* Three-operand version: ASR {<Rd>,} <Rn>, <Rm>. Here <Rm> is a
           * regular register and holds the value to shift the <Rn> register.
           * The operation must be explicitly done here.
           */
          else {
            auto& src2 = inst.operands[2];

            auto op2 = this->getArm32SourceOperandAst(inst, src2);

            node1 = this->astCtxt->bvror(
                      op1,
                      this->astCtxt->zx(
                        DWORD_SIZE_BIT-8,
                        this->astCtxt->extract(7, 0, op2)
                      )
                    );
          }

          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "ROR(S) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          auto taint = this->taintEngine->isTainted(src1);

          if (inst.operands.size() == 3) {
            auto& src2 = inst.operands[2];

            taint |= this->taintEngine->isTainted(src2);
          }

          this->spreadTaint(inst, cond, expr, dst, taint);

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            auto& src = inst.operands.size() == 2 ? inst.operands[1] : inst.operands[2];

            this->cfRor_s(inst, cond, expr, op1base, src);
            this->nf_s(inst, cond, expr, dst);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node2);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::rrx_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  cf  = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_C));

          /* Create symbolic operands */
          auto op1base = this->getArm32SourceBaseOperandAst(inst, src);
          auto op1     = this->getArm32SourceOperandAst(inst, src);
          auto op2     = this->getArm32SourceOperandAst(inst, cf);

          /* Create the semantics */
          auto node1 = this->astCtxt->extract(
                          op1->getBitvectorSize(),
                          1,
                          this->astCtxt->bvror(
                            this->astCtxt->concat(op1, op2),
                            1
                          )
                        );
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "RRX(S) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->cfRrx_s(inst, cond, expr, op1base, src);
            this->nf_s(inst, cond, expr, dst);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node2);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::rsb_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];
          auto& src2 = inst.operands[2];

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);
          auto op2 = this->getArm32SourceOperandAst(inst, src2);

          /* Create the semantics */
          auto node1 = this->astCtxt->bvsub(op2, op1);
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "RSB(S) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->cfSub_s(inst, cond, expr, dst, op2, op1);
            this->nf_s(inst, cond, expr, dst);
            this->vfSub_s(inst, cond, expr, dst, op2, op1);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node1);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::rsc_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];
          auto& src2 = inst.operands[2];
          auto  cf   = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_C));

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);
          auto op2 = this->getArm32SourceOperandAst(inst, src2);
          auto op3 = this->getArm32SourceOperandAst(inst, cf);

          /* Create the semantics */
          auto node1 = this->astCtxt->bvadd(
                          this->astCtxt->bvadd(op2, this->astCtxt->bvnot(op1)),
                          this->astCtxt->zx(dst.getBitSize()-1, op3)
                        );
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "RSB(S) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(cf));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->cfSub_s(inst, cond, expr, dst, op2, op1);
            this->nf_s(inst, cond, expr, dst);
            this->vfSub_s(inst, cond, expr, dst, op2, op1);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node1);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::sbc_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];
          auto& src2 = inst.operands[2];
          auto  cf   = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_C));

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);
          auto op2 = this->getArm32SourceOperandAst(inst, src2);
          auto op3 = this->getArm32SourceOperandAst(inst, cf);

          /* Create the semantics */
          auto node1 = this->astCtxt->bvadd(
                          this->astCtxt->bvadd(op1, this->astCtxt->bvnot(op2)),
                          this->astCtxt->zx(dst.getBitSize()-1, op3)
                        );
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "SBC(S) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(cf));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->cfSub_s(inst, cond, expr, dst, op1, op2);
            this->nf_s(inst, cond, expr, dst);
            this->vfSub_s(inst, cond, expr, dst, op1, op2);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node1);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::smull_s(triton::arch::Instruction& inst) {
          auto& dst1 = inst.operands[0];
          auto& dst2 = inst.operands[1];
          auto& src1 = inst.operands[2];
          auto& src2 = inst.operands[3];

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);
          auto op2 = this->getArm32SourceOperandAst(inst, src2);

          /* Create the semantics */
          auto cond  = this->getCodeConditionAst(inst);
          auto mul   = this->astCtxt->bvmul(
                          this->astCtxt->sx(QWORD_SIZE_BIT, op1),
                          this->astCtxt->sx(QWORD_SIZE_BIT, op2)
                        );
          auto lower = this->astCtxt->extract(DWORD_SIZE_BIT-1, 0, mul);
          auto upper = this->astCtxt->extract(QWORD_SIZE_BIT-1, DWORD_SIZE_BIT, mul);
          auto node1 = this->astCtxt->ite(cond, lower, this->symbolicEngine->getOperandAst(inst, dst1));
          auto node2 = this->astCtxt->ite(cond, upper, this->symbolicEngine->getOperandAst(inst, dst2));

          /* Create symbolic expression */
          auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst1, "SMULL(S) operation - Lower 32 bits of the result.");
          auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, dst2, "SMULL(S) operation - Upper 32 bits of the result.");

          /* Spread taint */
          this->spreadTaint(inst, cond, expr1, dst1, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));
          this->spreadTaint(inst, cond, expr2, dst2, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->nfSmull_s(inst, cond, expr1, expr2, dst1, dst2);
            this->zfSmull_s(inst, cond, expr1, expr2, dst1, dst2);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            /* NOTE: The invocations are done in the order the manual says
             * the instruction updates each register. Examples for this case
             * could be:
             *   - smull pc, r1, r2, r3
             *   - smull pc, pc, r2, r3
             */
            this->updateExecutionState(dst2, upper);
            this->updateExecutionState(dst1, lower);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst1, dst2);
        }


        void Arm32Semantics::stm_s(triton::arch::Instruction& inst) {
          auto& base          = inst.operands[0];
          triton::uint32 size = DWORD_SIZE;

          /* Create symbolic operands */
          auto baseNode = this->symbolicEngine->getOperandAst(inst, base);

          /* Create the semantics */
          auto cond = this->getCodeConditionAst(inst);

          for (unsigned int i = 1; i < inst.operands.size(); i++) {
            auto& src = inst.operands[i];

            /* Compute memory address */
            auto addr = baseNode->evaluate().convert_to<triton::uint64>() + size * (i-1);
            auto dst  = triton::arch::OperandWrapper(triton::arch::MemoryAccess(addr, size));

            /* Create symbolic operands */
            auto op2 = this->symbolicEngine->getOperandAst(inst, src);
            auto op3 = this->symbolicEngine->getOperandAst(inst, dst);

            /* Create the semantics */
            auto node = this->astCtxt->ite(cond, op2, op3);

            /* Create symbolic expression */
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "STM operation - STORE access");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr1, dst, this->taintEngine->isTainted(base) | this->taintEngine->isTainted(src));
          }

          if (inst.isWriteBack() == true) {
            /* Create the semantics of the base register */
            auto node = this->astCtxt->ite(
                            cond,
                            this->astCtxt->bvadd(
                              baseNode,
                              this->astCtxt->bv((inst.operands.size() - 1) * size, base.getBitSize())
                            ),
                            baseNode
                          );

            /* Create symbolic expression */
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node, base, "STM operation - Base register computation");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr2, base, this->taintEngine->isTainted(base));
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst);
        }


        void Arm32Semantics::stmib_s(triton::arch::Instruction& inst) {
          auto& base          = inst.operands[0];
          triton::uint32 size = DWORD_SIZE;

          /* Create symbolic operands */
          auto baseNode = this->symbolicEngine->getOperandAst(inst, base);

          /* Create the semantics */
          auto cond = this->getCodeConditionAst(inst);

          for (unsigned int i = 1; i < inst.operands.size(); i++) {
            auto& src = inst.operands[i];

            /* Compute memory address */
            auto addr = baseNode->evaluate().convert_to<triton::uint64>() + size * i;
            auto dst  = triton::arch::OperandWrapper(triton::arch::MemoryAccess(addr, size));

            /* Create symbolic operands */
            auto op2 = this->symbolicEngine->getOperandAst(inst, src);
            auto op3 = this->symbolicEngine->getOperandAst(inst, dst);

            /* Create the semantics */
            auto node = this->astCtxt->ite(cond, op2, op3);

            /* Create symbolic expression */
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "STMIB operation - STORE access");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr1, dst, this->taintEngine->isTainted(base) | this->taintEngine->isTainted(src));
          }

          if (inst.isWriteBack() == true) {
            /* Create the semantics of the base register */
            auto node1 = this->astCtxt->ite(
                            cond,
                            this->astCtxt->bvadd(
                              baseNode,
                              this->astCtxt->bv((inst.operands.size() - 1) * size, base.getBitSize())
                            ),
                            baseNode
                          );

            /* Create symbolic expression */
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node1, base, "STMIB operation - Base register computation");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr2, base, this->taintEngine->isTainted(base));
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst);
        }


        void Arm32Semantics::str_s(triton::arch::Instruction& inst) {
          auto& src = inst.operands[0];
          auto& dst = inst.operands[1];

          /* Create symbolic operands */
          auto op = this->getArm32SourceOperandAst(inst, src);

          /* Create the semantics */
          auto node1 = this->buildConditionalSemantics(inst, dst, op);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "STR operation - STORE access");

          /* Get condition code node */
          auto cond = node1->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src));

          /* Optional behavior. Post-indexed computation of the base register. */
          /* STR <Rt>, [<Rn>], #+/-<imm> */
          if (inst.operands.size() == 3) {
            auto& imm  = inst.operands[2].getImmediate();
            auto& base = dst.getMemory().getBaseRegister();

            /* Create symbolic operands of the post computation */
            auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
            auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

            /* Create the semantics of the base register */
            auto thenNode = this->astCtxt->bvadd(baseNode, this->astCtxt->sx(base.getBitSize() - imm.getBitSize(), immNode));

            if (imm.getSubtracted() == true) {
              thenNode = this->astCtxt->bvsub(baseNode, this->astCtxt->sx(base.getBitSize() - imm.getBitSize(), immNode));
            }

            auto node2 = this->astCtxt->ite(cond, thenNode, baseNode);

            /* Create symbolic expression */
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "STR operation - Base register computation");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr2, base, this->taintEngine->isTainted(base));
          }

          /* Optional behavior. Pre-indexed computation of the base register. */
          /* STR <Rt>, [<Rn>, #+/-<imm>]! */
          else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
            auto& base = dst.getMemory().getBaseRegister();

            /* Create symbolic operands of the post computation */
            auto baseNode = this->symbolicEngine->getOperandAst(inst, base);

            /* Create the semantics of the base register */
            auto node3 = this->astCtxt->ite(cond, dst.getMemory().getLeaAst(), baseNode);

            /* Create symbolic expression */
            auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "STR operation - Base register computation");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr3, base, this->taintEngine->isTainted(base));
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst);
        }


        void Arm32Semantics::strb_s(triton::arch::Instruction& inst) {
          auto& src = inst.operands[0];
          auto& dst = inst.operands[1];

          /* Create symbolic operands */
          auto op = this->getArm32SourceOperandAst(inst, src);

          /* Special behavior: Define that the size of the memory access is 8 bits */
          dst.getMemory().setPair(std::make_pair(7, 0));

          /* Create the semantics */
          auto node  = this->astCtxt->extract(7, 0, op);
          auto node1 = this->buildConditionalSemantics(inst, dst, node);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "STRB operation - STORE access");

          /* Get condition code node */
          auto cond = node1->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src));

          /* Optional behavior. Post-indexed computation of the base register. */
          /* STRB <Rt>, [<Rn>], #+/-<imm> */
          if (inst.operands.size() == 3) {
            auto& imm  = inst.operands[2].getImmediate();
            auto& base = dst.getMemory().getBaseRegister();

            /* Create symbolic operands of the post computation */
            auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
            auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

            /* Create the semantics of the base register */
            auto thenNode = this->astCtxt->bvadd(baseNode, this->astCtxt->sx(base.getBitSize() - imm.getBitSize(), immNode));

            if (imm.getSubtracted() == true) {
              thenNode = this->astCtxt->bvsub(baseNode, this->astCtxt->sx(base.getBitSize() - imm.getBitSize(), immNode));
            }

            auto node2 = this->astCtxt->ite(cond, thenNode, baseNode);

            /* Create symbolic expression */
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "STRB operation - Base register computation");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr2, base, this->taintEngine->isTainted(base));
          }

          /* Optional behavior. Pre-indexed computation of the base register. */
          /* STRB <Rt>, [<Rn>, #+/-<imm>]! */
          else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
            auto& base = dst.getMemory().getBaseRegister();

            /* Create symbolic operands of the post computation */
            auto baseNode = this->symbolicEngine->getOperandAst(inst, base);

            /* Create the semantics of the base register */
            auto node3 = this->astCtxt->ite(cond, dst.getMemory().getLeaAst(), baseNode);

            /* Create symbolic expression */
            auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "STRB operation - Base register computation");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr3, base, this->taintEngine->isTainted(base));
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst);
        }


        void Arm32Semantics::strd_s(triton::arch::Instruction& inst) {
          auto& base          = inst.operands[2];
          triton::uint32 size = DWORD_SIZE;

          /* Create the semantics */
          auto cond = this->getCodeConditionAst(inst);

          for (unsigned int i = 0; i < 2; i++) {
            auto& src = inst.operands[i];

            /* Compute memory address */
            auto addr = base.getMemory().getAddress() + size * i;
            auto dst  = triton::arch::OperandWrapper(triton::arch::MemoryAccess(addr, size));

            /* Create symbolic operands */
            auto op2 = this->symbolicEngine->getOperandAst(inst, src);
            auto op3 = this->symbolicEngine->getOperandAst(inst, dst);

            /* Create the semantics */
            auto node = this->astCtxt->ite(cond, op2, op3);

            /* Create symbolic expression */
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "STRD operation - STORE access");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr1, dst, this->taintEngine->isTainted(base) | this->taintEngine->isTainted(src));
          }

          /* Optional behavior. Post-indexed computation of the base register. */
          /* STRD <Rt>, <Rt2>, [<Rn>], #+/-<imm>; STRD <Rt>, <Rt2>, [<Rn>], +/-<Rm>*/
          if (inst.operands.size() == 4) {
            /* TODO (cnheitman): Differenciate between imm and reg operand (as in STRH).*/
            auto& imm  = inst.operands[3].getImmediate();
            auto& base = inst.operands[2].getMemory().getBaseRegister();

            /* Create symbolic operands of the post computation */
            auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
            auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

            /* Create the semantics of the base register */
            auto node2 = this->astCtxt->ite(
                            cond,
                            this->astCtxt->bvadd(baseNode, this->astCtxt->sx(base.getBitSize() - imm.getBitSize(), immNode)),
                            baseNode
                            );

            /* Create symbolic expression */
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "STRD operation - Base register computation");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr2, base, this->taintEngine->isTainted(base));
          }

          /* Optional behavior. Pre-indexed computation of the base register. */
          /* STR <Rt>, <Rt2>, [<Rn>, #+/-<imm>]! */
          else if (inst.operands.size() == 3 && inst.isWriteBack() == true) {
            auto& base = inst.operands[2].getMemory().getBaseRegister();

            /* Create symbolic operands of the post computation */
            auto baseNode = this->symbolicEngine->getOperandAst(inst, base);

            /* Create the semantics of the base register */
            auto node3 = this->astCtxt->ite(cond, inst.operands[2].getMemory().getLeaAst(), baseNode);

            /* Create symbolic expression */
            auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "STRD operation - Base register computation");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr3, base, this->taintEngine->isTainted(base));
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst);
        }


        void Arm32Semantics::strh_s(triton::arch::Instruction& inst) {
          auto& src = inst.operands[0];
          auto& dst = inst.operands[1];

          /* Create symbolic operands */
          auto op = this->getArm32SourceOperandAst(inst, src);

          /* Special behavior: Define that the size of the memory access is 16 bits */
          dst.getMemory().setPair(std::make_pair(15, 0));

          /* Create the semantics */
          auto node1 = this->astCtxt->extract(15, 0, op);
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "STRH operation - STORE access");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src));

          /* Optional behavior. Post-indexed computation of the base register. */
          /* STRH <Rt>, [<Rn>], #+/-<imm>; STRH <Rt>, [<Rn>], +/-<Rm>*/
          if (inst.operands.size() == 3) {
            /* TODO (cnheitman): Refactor. */
            if (inst.operands[2].getType() == OP_IMM) {
              auto& imm  = inst.operands[2].getImmediate();
              auto& base = dst.getMemory().getBaseRegister();

              /* Create symbolic operands of the post computation */
              auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
              auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

              /* Create the semantics of the base register */
              auto thenNode = this->astCtxt->bvadd(baseNode, this->astCtxt->sx(base.getBitSize() - imm.getBitSize(), immNode));

              if (imm.getSubtracted() == true) {
                thenNode = this->astCtxt->bvsub(baseNode, this->astCtxt->sx(base.getBitSize() - imm.getBitSize(), immNode));
              }

              auto node2 = this->astCtxt->ite(cond, thenNode, baseNode);

              /* Create symbolic expression */
              auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "STRH operation - Base register computation");

              /* Spread taint */
              this->spreadTaint(inst, cond, expr2, base, this->taintEngine->isTainted(base));
            } else {
              auto& reg  = inst.operands[2].getRegister();
              auto& base = dst.getMemory().getBaseRegister();

              /* Create symbolic operands of the post computation */
              auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
              auto regNode  = this->symbolicEngine->getOperandAst(inst, reg);

              /* Create the semantics of the base register */
              auto thenNode = this->astCtxt->bvadd(baseNode, regNode);

              if (reg.getSubtracted() == true) {
                thenNode = this->astCtxt->bvsub(baseNode, regNode);
              }

              auto node2 = this->astCtxt->ite(cond, thenNode, baseNode);

              /* Create symbolic expression */
              auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "STRH operation - Base register computation");

              /* Spread taint */
              this->spreadTaint(inst, cond, expr2, base, this->taintEngine->isTainted(base) | this->taintEngine->isTainted(reg));
            }
          }

          /* Optional behavior. Pre-indexed computation of the base register. */
          /* STRH <Rt>, [<Rn>, #+/-<imm>]! */
          else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
            auto& base = dst.getMemory().getBaseRegister();

            /* Create symbolic operands of the post computation */
            auto baseNode = this->symbolicEngine->getOperandAst(inst, base);

            /* Create the semantics of the base register */
            auto node3 = this->astCtxt->ite(cond, dst.getMemory().getLeaAst(), baseNode);

            /* Create symbolic expression */
            auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "STRH operation - Base register computation");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr3, base, this->taintEngine->isTainted(base));
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::sub_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];
          auto& src2 = inst.operands[2];

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);
          auto op2 = this->getArm32SourceOperandAst(inst, src2);

          /* Create the semantics */
          auto node1 = this->astCtxt->bvsub(op1, op2);
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "SUB(S) operation");

          /* Get condition code node */
          auto cond = node2->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->cfSub_s(inst, cond, expr, dst, op1, op2);
            this->nf_s(inst, cond, expr, dst);
            this->vfSub_s(inst, cond, expr, dst, op1, op2);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Update swtich mode accordingly. */
            this->updateExecutionState(dst, node1);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::tst_s(triton::arch::Instruction& inst) {
          auto& src1 = inst.operands[0];
          auto& src2 = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);
          auto op2 = this->getArm32SourceOperandAst(inst, src2);

          /* Create the semantics */
          auto cond  = this->getCodeConditionAst(inst);
          auto node1 = this->astCtxt->bvand(op1, op2);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "TST operation");

          /* Update symbolic flags */
          this->cfBitwise_s(inst, cond, expr, src2);
          this->nf_s(inst, cond, expr, src1);
          this->zf_s(inst, cond, expr, src1);

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst);
        }


        void Arm32Semantics::cfBitwise_s(triton::arch::Instruction& inst,
                                         const triton::ast::SharedAbstractNode& cond,
                                         const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                         triton::arch::OperandWrapper& src) {

          /* TODO (cnheitman): Check if we can use the same prototype as the
           * rest of the functions that process the CF.
           */

          auto cf = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_C));

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src);

          /* Create the semantics */
          triton::ast::SharedAbstractNode node = nullptr;
          triton::arch::arm::shift_e shiftType = triton::arch::arm::ID_SHIFT_INVALID;
          triton::ast::SharedAbstractNode shiftAmount = nullptr;

          switch (src.getType()) {
            /* TODO (cnheitman): Comment each case. */

            case triton::arch::OP_IMM: {
              /* From ARMExpandImm_C():
               *    unrotated_value = ZeroExtend(imm12<7:0>, 32);
               *    (imm32, carry_out) = Shift_C(unrotated_value, SRType_ROR, 2*UInt(imm12<11:8>), carry_in);
               */

              node = this->astCtxt->zx(DWORD_SIZE_BIT-8, this->astCtxt->extract(7, 0, op1));
              shiftType = triton::arch::arm::ID_SHIFT_ROR;
              shiftAmount = this->astCtxt->bv(
                              2 * (src.getImmediate().getValue() & 0x00000f00),
                              node->getBitvectorSize()
                            );
              break;
            }

            case triton::arch::OP_REG: {
              if (src.getRegister().getShiftType() != triton::arch::arm::ID_SHIFT_INVALID) {
                auto shift = static_cast<const triton::arch::arm::ArmOperandProperties>(src.getRegister());

                /* NOTE: This is a hacky way to obtain the ast of the operand
                 * without the shift. This has to be done before building the
                 * semantics (the current value is needed, not the new one).
                 */
                /* TODO (cnheitman): Improve this code. */
                auto srcBase = triton::arch::OperandWrapper(src.getRegister());
                srcBase.getRegister().setShiftType(triton::arch::arm::ID_SHIFT_INVALID);

                node = this->symbolicEngine->getOperandAst(inst, srcBase);
                shiftAmount = this->getShiftCAmountAst(shift);
                shiftType = this->getShiftCBaseType(shift);
              } else {
                /* From the instruction decoding:
                 *    (shift_t, shift_n) = (SRType_LSL, 0);
                 */

                node = op1;
                shiftType = triton::arch::arm::ID_SHIFT_LSL;
                shiftAmount = this->astCtxt->bv(0, op1->getBitvectorSize());
              }
              break;
            }

            default:
              throw triton::exceptions::Semantics("Arm32Semantics::cfBitwise_s(): Invalid operand type.");
          }

          /* Create the semantics */
          auto node1 = this->getShiftCAst(node, shiftType, shiftAmount);
          auto node2 = this->symbolicEngine->getOperandAst(cf);
          auto node3 = this->astCtxt->ite(cond, node1, node2);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node3, cf, "Carry flag");

          /* Spread the taint from the parent to the child */
          this->spreadTaint(inst, cond, expr, cf, parent->isTainted);
        }


        void Arm32Semantics::cfShift_s(triton::arch::Instruction& inst,
                                        const triton::ast::SharedAbstractNode& cond,
                                        const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                        const triton::ast::SharedAbstractNode& op1,
                                        triton::arch::OperandWrapper& src,
                                        const triton::arch::arm::shift_e type) {
          /* IMPORTANT: We asume that op1 is a register without its shift. */

          /* TODO (cnheitman): Check if we can use the same prototype as the
           * rest of the functions that process the CF.
           */

          auto cf = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_C));

          /* Create the semantics */
          triton::ast::SharedAbstractNode node = nullptr;
          triton::arch::arm::shift_e shiftType = type;
          triton::ast::SharedAbstractNode shiftAmount = nullptr;

          switch (src.getType()) {
            /* TODO (cnheitman): Comment each case. */

            case triton::arch::OP_IMM: {
              shiftAmount = this->astCtxt->bv(src.getImmediate().getValue(), op1->getBitvectorSize());
              break;
            }

            case triton::arch::OP_REG: {
              if (src.getRegister().getShiftType() != triton::arch::arm::ID_SHIFT_INVALID) {
                auto shift = static_cast<const triton::arch::arm::ArmOperandProperties>(src.getRegister());

                shiftAmount = this->getShiftCAmountAst(shift);
                shiftType = this->getShiftCBaseType(shift);
              } else {
                // (result, carry) = Shift_C(R[m], SRType_XXX, shift_n, APSR.C);

                /* Create symbolic operands */
                auto op2 = this->getArm32SourceOperandAst(inst, src);

                /* Create the semantics */
                shiftAmount = this->astCtxt->zx(DWORD_SIZE_BIT-8, this->astCtxt->extract(7, 0, op2));

                /* Special case for instruction RRX. */
                if (type == triton::arch::arm::ID_SHIFT_RRX) {
                  shiftAmount = this->astCtxt->bv(1, op1->getBitvectorSize());
                }
              }
              break;
            }

            default:
              throw triton::exceptions::Semantics("Arm32Semantics::cfShift_s(): Invalid operand type.");
          }

          /* Create the semantics */
          auto node1 = this->getShiftCAst(op1, shiftType, shiftAmount);
          auto node2 = this->symbolicEngine->getOperandAst(cf);
          auto node3 = this->astCtxt->ite(cond, node1, node2);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node3, cf, "Carry flag");

          /* Spread the taint from the parent to the child */
          this->spreadTaint(inst, cond, expr, cf, parent->isTainted);
        }


        void Arm32Semantics::cfAsr_s(triton::arch::Instruction& inst,
                                     const triton::ast::SharedAbstractNode& cond,
                                     const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                     const triton::ast::SharedAbstractNode& op1,
                                     triton::arch::OperandWrapper& src) {

          this->cfShift_s(inst, cond, parent, op1, src, triton::arch::arm::ID_SHIFT_ASR);
        }


        void Arm32Semantics::cfLsl_s(triton::arch::Instruction& inst,
                                     const triton::ast::SharedAbstractNode& cond,
                                     const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                     const triton::ast::SharedAbstractNode& op1,
                                     triton::arch::OperandWrapper& src) {

          this->cfShift_s(inst, cond, parent, op1, src, triton::arch::arm::ID_SHIFT_LSL);
        }


        void Arm32Semantics::cfLsr_s(triton::arch::Instruction& inst,
                                     const triton::ast::SharedAbstractNode& cond,
                                     const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                     const triton::ast::SharedAbstractNode& op1,
                                     triton::arch::OperandWrapper& src) {

          this->cfShift_s(inst, cond, parent, op1, src, triton::arch::arm::ID_SHIFT_LSR);
        }


        void Arm32Semantics::cfRor_s(triton::arch::Instruction& inst,
                                     const triton::ast::SharedAbstractNode& cond,
                                     const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                     const triton::ast::SharedAbstractNode& op1,
                                     triton::arch::OperandWrapper& src) {

          this->cfShift_s(inst, cond, parent, op1, src, triton::arch::arm::ID_SHIFT_ROR);
        }


        void Arm32Semantics::cfRrx_s(triton::arch::Instruction& inst,
                                     const triton::ast::SharedAbstractNode& cond,
                                     const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                     const triton::ast::SharedAbstractNode& op1,
                                     triton::arch::OperandWrapper& src) {

          this->cfShift_s(inst, cond, parent, op1, src, triton::arch::arm::ID_SHIFT_RRX);
        }


        triton::ast::SharedAbstractNode Arm32Semantics::getShiftCAst(const triton::ast::SharedAbstractNode& node,
                                                                     const triton::arch::arm::shift_e type,
                                                                     const triton::ast::SharedAbstractNode& shifAmount) {

          /* NOTE This function implements the Shift_C function from the
           * reference manual:
           *
           * (bits(N), bit) Shift_C(bits(N) value, SRType type, integer amount, bit carry_in)
           *
           * However, it only returns the carry out. Check the reference manual
           * for more information.
           */

          auto cf = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_C));

          /* Set carry out node to the current value of the carry (carry in). */
          triton::ast::SharedAbstractNode carryOutNode = this->symbolicEngine->getOperandAst(cf);

          /* TODO (cnheitman): Make amount symbolic. */
          uint32 amount = shifAmount->evaluate().convert_to<triton::uint32>();

          if (amount == 0)
            return carryOutNode;

          switch (type) {
            case triton::arch::arm::ID_SHIFT_ASR: {
              auto extendedX = this->astCtxt->sx(amount, node);
              carryOutNode = this->astCtxt->extract(amount-1, amount-1, extendedX);
              break;
            }

            case triton::arch::arm::ID_SHIFT_LSL: {
              auto extendedX = this->astCtxt->concat(node, this->astCtxt->bv(0, amount));
              carryOutNode = this->astCtxt->extract(DWORD_SIZE_BIT, DWORD_SIZE_BIT, extendedX);
              break;
            }

            case triton::arch::arm::ID_SHIFT_LSR: {
              auto extendedX = this->astCtxt->zx(amount, node);
              carryOutNode = this->astCtxt->extract(amount-1, amount-1, extendedX);
              break;
            }

            case triton::arch::arm::ID_SHIFT_ROR: {
              auto result = this->ror_c(node, amount);
              carryOutNode = this->astCtxt->extract(DWORD_SIZE_BIT-1, DWORD_SIZE_BIT-1, result);
              break;
            }

            case triton::arch::arm::ID_SHIFT_RRX: {
              carryOutNode = this->astCtxt->extract(0, 0, node);
              break;
            }

            default:
              throw triton::exceptions::Semantics("Arm32Semantics::getShiftCAst(): Invalid shift operand.");
          }

          return carryOutNode;
        }


        triton::arch::arm::shift_e Arm32Semantics::getShiftCBaseType(const triton::arch::arm::ArmOperandProperties& shift) {
          triton::arch::arm::shift_e type = triton::arch::arm::ID_SHIFT_INVALID;

          switch (shift.getShiftType()) {
            case triton::arch::arm::ID_SHIFT_ASR:
            case triton::arch::arm::ID_SHIFT_LSL:
            case triton::arch::arm::ID_SHIFT_LSR:
            case triton::arch::arm::ID_SHIFT_ROR:
            case triton::arch::arm::ID_SHIFT_RRX:
              type = shift.getShiftType();
              break;

            case triton::arch::arm::ID_SHIFT_ASR_REG:
              type = triton::arch::arm::ID_SHIFT_ASR;
              break;

            case triton::arch::arm::ID_SHIFT_LSL_REG:
              type = triton::arch::arm::ID_SHIFT_LSL;
              break;

            case triton::arch::arm::ID_SHIFT_LSR_REG:
              type = triton::arch::arm::ID_SHIFT_LSR;
              break;

            case triton::arch::arm::ID_SHIFT_ROR_REG:
              type = triton::arch::arm::ID_SHIFT_ROR;
              break;

            case triton::arch::arm::ID_SHIFT_RRX_REG:
              /* NOTE: Capstone considers this as a viable shift operand but
               * according to the ARM manual this is not possible.
               */
              throw triton::exceptions::Semantics("Arm32Semantics::getShiftCBasicType(): ID_SHIFT_RRX_REG is an invalid shift operand.");

            default:
              throw triton::exceptions::Semantics("Arm32Semantics::getShiftCBasicType(): Invalid shift operand.");
          }

          return type;
        }


        triton::ast::SharedAbstractNode Arm32Semantics::getShiftCAmountAst(const triton::arch::arm::ArmOperandProperties& shift) {
          auto imm = shift.getShiftImmediate();
          auto reg = shift.getShiftRegister();

          triton::ast::SharedAbstractNode amount;
          triton::ast::SharedAbstractNode immShiftAmount = this->astCtxt->bv(imm, DWORD_SIZE_BIT);
          triton::ast::SharedAbstractNode regShiftAmount = nullptr;

          if (reg != triton::arch::ID_REG_INVALID) {
            auto op = this->symbolicEngine->getRegisterAst(this->architecture->getRegister(reg));

            regShiftAmount = this->astCtxt->zx(
                                this->architecture->getRegister(reg).getBitSize()-8,
                                this->astCtxt->extract(7, 0, op)
                              );
          }

          switch (shift.getShiftType()) {
            case triton::arch::arm::ID_SHIFT_ASR:
            case triton::arch::arm::ID_SHIFT_LSL:
            case triton::arch::arm::ID_SHIFT_LSR:
            case triton::arch::arm::ID_SHIFT_ROR:
            case triton::arch::arm::ID_SHIFT_RRX:
              amount = immShiftAmount;
              break;

            case triton::arch::arm::ID_SHIFT_ASR_REG:
            case triton::arch::arm::ID_SHIFT_LSL_REG:
            case triton::arch::arm::ID_SHIFT_LSR_REG:
            case triton::arch::arm::ID_SHIFT_ROR_REG:
              amount = regShiftAmount;
              break;

            case triton::arch::arm::ID_SHIFT_RRX_REG:
              /* NOTE: Capstone considers this as a viable shift operand but
               * according to the ARM manual this is not possible.
               */
              throw triton::exceptions::Semantics("Arm32Semantics::getShiftCAmountAst(): ID_SHIFT_RRX_REG is an invalid shift operand.");

            default:
              throw triton::exceptions::Semantics("Arm32Semantics::getShiftCAmountAst(): Invalid shift operand.");
          }

          return amount;
        }


        triton::ast::SharedAbstractNode Arm32Semantics::lsl_c(const triton::ast::SharedAbstractNode& node, uint32 shift) {
          if (shift > 0) {
            auto extendedX = this->astCtxt->concat(node, this->astCtxt->bv(0, shift));
            auto result = this->astCtxt->extract(DWORD_SIZE_BIT-1, 0, extendedX);
            return result;
          } else {
            return nullptr;
          }
        }


        triton::ast::SharedAbstractNode Arm32Semantics::lsl(const triton::ast::SharedAbstractNode& node, uint32 shift) {
          if (shift == 0) {
            return node;
          } else {
            return this->lsl_c(node, shift);
          }
        }


        triton::ast::SharedAbstractNode Arm32Semantics::lsr_c(const triton::ast::SharedAbstractNode& node, uint32 shift) {
          if (shift > 0) {
            auto extendedX = this->astCtxt->zx(shift, node);
            auto result = this->astCtxt->extract(shift+DWORD_SIZE_BIT-1, shift, extendedX);
            return result;
          } else {
            return nullptr;
          }
        }


        triton::ast::SharedAbstractNode Arm32Semantics::lsr(const triton::ast::SharedAbstractNode& node, uint32 shift) {
          if (shift == 0) {
            return node;
          } else {
            return this->lsr_c(node, shift);
          }
        }


        triton::ast::SharedAbstractNode Arm32Semantics::ror_c(const triton::ast::SharedAbstractNode& node, uint32 shift) {
          if (shift == 0) {
            return nullptr;
          } else {
            auto m = shift % DWORD_SIZE_BIT;
            auto result = this->astCtxt->bvor(this->lsr(node, m), this->lsl(node, DWORD_SIZE_BIT-m));
            return result;
          }
        }


        triton::ast::SharedAbstractNode Arm32Semantics::ror(const triton::ast::SharedAbstractNode& node, uint32 shift) {
          if (shift == 0) {
            return node;
          } else {
            return this->ror_c(node, shift);
          }
        }
      }; /* arm32 namespace */
    }; /* arm namespace */
  }; /* arch namespace */
}; /* triton namespace */
