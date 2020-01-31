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


#include <iostream>


/*! \page SMT_arm32_Semantics_Supported_page ARM32 SMT semantics supported
    \brief [**internal**] List of the supported semantics for the ARM32 architecture.


Mnemonic                      | Description
------------------------------|------------
ADC                           | Add with Carry
ADCS                          | Add with Carry, setting flags
ADD                           | Add
ADDS                          | Add, setting flags
AND                           | Bitwise AND
ASR                           | Arithmetic Shift Right
B                             | Branch
BL                            | Branch with Link
BLX                           | Branch with Link and Exchange
BX                            | Branch and Exchange
CLZ                           | Count Leading Zeros
CMP                           | Compare
EOR                           | Bitwise Exclusive OR
LDR                           | Load Register
LDRB                          | Load Register Byte
LSL                           | Logical Shift Left
LSR                           | Logical Shift Right
MOV                           | Move Register
MUL                           | Multiply
ORR                           | Bitwise OR
POP                           | Pop Multiple Registers
PUSH                          | Push Multiple Registers
RSB                           | Reverse Subtract
SMULL                         | Signed Multiply Long
STR                           | Store Register
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
            case ID_INS_ASR:       this->asr_s(inst);           break;
            case ID_INS_AND:       this->and_s(inst);           break;
            case ID_INS_B:         this->b_s(inst);             break;
            case ID_INS_BL:        this->bl_s(inst, false);     break;
            case ID_INS_BLX:       this->bl_s(inst, true);      break;
            case ID_INS_BX:        this->bx_s(inst);            break;
            case ID_INS_CLZ:       this->clz_s(inst);           break;
            case ID_INS_CMP:       this->cmp_s(inst);           break;
            case ID_INS_EOR:       this->eor_s(inst);           break;
            case ID_INS_LDR:       this->ldr_s(inst);           break;
            case ID_INS_LDRB:      this->ldrb_s(inst);          break;
            case ID_INS_LSL:       this->lsl_s(inst);           break;
            case ID_INS_LSR:       this->lsr_s(inst);           break;
            case ID_INS_MOV:       this->mov_s(inst);           break;
            case ID_INS_MUL:       this->mul_s(inst);           break;
            case ID_INS_ORR:       this->orr_s(inst);           break;
            case ID_INS_POP:       this->pop_s(inst);           break;
            case ID_INS_PUSH:      this->push_s(inst);          break;
            case ID_INS_RSB:       this->rsb_s(inst);           break;
            case ID_INS_SMULL:     this->smull_s(inst);         break;
            case ID_INS_STR:       this->str_s(inst);           break;
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


        inline triton::ast::SharedAbstractNode Arm32Semantics::getArm32SourceOperandAst(triton::arch::Instruction& inst,
                                                                                        triton::arch::OperandWrapper& op) {
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
                                         triton::arch::OperandWrapper& operand,
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
          /* TODO (cnheitman): Apply this to ADC and SUB. */
          if (inst.operands.size() == 4) {
            auto size  = src2.getSize();
            auto value = src2.getImmediate().getValue();
            auto shift = inst.operands[3].getImmediate().getValue();

            src2 = triton::arch::Immediate(this->ror(value, shift), size);
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
            /* TODO (cnheitman): There is an issue here. The manual says that
             * the carry flag should be updated but when we test it against
             * Unicorn it is not update. Bug in UC? Disabling it for now.
             */
            // this->cfAdd_s(inst, cond, expr, dst, op1, op2);
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
          auto op1 = this->getArm32SourceOperandAst(inst, src1);

          auto node1 = this->buildConditionalSemantics(inst, dst, op1);

          if (inst.operands.size() == 3) {
            auto& src2 = inst.operands[2];

            auto op2 = this->getArm32SourceOperandAst(inst, src2);

            auto node = this->astCtxt->bvashr(
                          op1,
                          this->astCtxt->zx(
                            DWORD_SIZE_BIT-8,
                            this->astCtxt->extract(7, 0, op2)
                          )
                        );
            node1 = this->buildConditionalSemantics(inst, dst, node);
          }

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "ASR(S) operation");

          /* Get condition code node */
          auto cond = node1->getChildren()[0];

          /* Spread taint */
          if (inst.operands.size() == 2) {
            this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1));
          } else {
            auto& src2 = inst.operands[2];

            this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));
          }

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            /* TODO (cnheitman): Implement. */
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


        void Arm32Semantics::bl_s(triton::arch::Instruction& inst, bool exchange) {
          auto  dst1 = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_R14));
          auto  dst2 = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_PC));
          auto& src = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src);
          auto op2 = this->symbolicEngine->getOperandAst(inst, dst1);
          auto op3 = this->symbolicEngine->getOperandAst(inst, dst2);
          auto op4 = this->astCtxt->bv(inst.getNextAddress(), dst2.getBitSize());

          /* Create the semantics */
          auto cond  = this->getCodeConditionAst(inst);

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
          auto cond  = this->getCodeConditionAst(inst);

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
          // auto node2 = this->astCtxt->ite(cond, node1, this->astCtxt->bvtrue());

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
            /* TODO (cnheitman): There is an issue here. The manual says that
             * the carry flag should be updated but when we test it against
             * Unicorn it is not update. Bug in UC? Disabling it for now.
             */
            // this->cfAdd_s(inst, cond, expr, dst, op1, op2);
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


        void Arm32Semantics::ldr_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          // auto op = this->getArm32SourceOperandAst(inst, src);
          auto op = this->symbolicEngine->getOperandAst(inst, src);

          /* Create the semantics */
          auto node1 = this->buildConditionalSemantics(inst, dst, op);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "LDR operation - LOAD access");

          /* Get condition code node */
          auto cond = node1->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src));

          /* Optional behavior. Post-indexed computation of the base register */
          /* LDR <Rt>, [<Rn], #<simm> */
          if (inst.operands.size() == 3) {
            auto& imm = inst.operands[2].getImmediate();
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
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "LDR operation - Post-indexed base register computation");

            /* TODO: Fix.*/
            /* Spread taint */
            // this->spreadTaint(inst, cond, expr2, base, this->taintEngine->isTainted(base));
          }

          /* Optional behavior. Pre-indexed computation of the base register */
          /* LDR <Rt>, [<Rn>, #<simm>]! */
          else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
            auto& base = src.getMemory().getBaseRegister();

            /* Create symbolic operands of the post computation */
            auto baseNode = this->symbolicEngine->getOperandAst(inst, base);

            /* Create the semantics of the base register */
            auto node3 = this->astCtxt->ite(
                            cond,
                            src.getMemory().getLeaAst(),
                            baseNode
                          );

            /* Create symbolic expression */
            auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "LDR operation - Pre-indexed base register computation");

            /* TODO: Fix.*/
            /* Spread taint */
            // this->spreadTaint(inst, cond, expr3, base, this->taintEngine->isTainted(base));
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
          auto& dst  = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          // auto op = this->getArm32SourceOperandAst(inst, src);
          auto op = this->symbolicEngine->getOperandAst(inst, src);

          /* Create the semantics */
          auto node = this->astCtxt->zx(dst.getBitSize() - src.getBitSize(), op);
          auto node1 = this->buildConditionalSemantics(inst, dst, node);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "LDRB operation - LOAD access");

          /* Get condition code node */
          auto cond = node1->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src));

          /* Optional behavior. Post-indexed computation of the base register */
          /* LDR <Rt>, [<Rn], #<simm> */
          if (inst.operands.size() == 3) {
            auto& imm = inst.operands[2].getImmediate();
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
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "LDR operation - Post-indexed base register computation");

            /* TODO: Fix.*/
            /* Spread taint */
            // this->spreadTaint(inst, cond, expr2, base, this->taintEngine->isTainted(base));
          }

          /* Optional behavior. Pre-indexed computation of the base register */
          /* LDR <Rt>, [<Rn>, #<simm>]! */
          else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
            auto& base = src.getMemory().getBaseRegister();

            /* Create symbolic operands of the post computation */
            auto baseNode = this->symbolicEngine->getOperandAst(inst, base);

            /* Create the semantics of the base register */
            auto node3 = this->astCtxt->ite(
                            cond,
                            src.getMemory().getLeaAst(),
                            baseNode
                          );

            /* Create symbolic expression */
            auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "LDR operation - Pre-indexed base register computation");

            /* TODO: Fix.*/
            /* Spread taint */
            // this->spreadTaint(inst, cond, expr3, base, this->taintEngine->isTainted(base));
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


        void Arm32Semantics::lsl_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);

          auto node1 = this->buildConditionalSemantics(inst, dst, op1);

          if (inst.operands.size() == 3) {
            auto& src2 = inst.operands[2];

            auto op2 = this->getArm32SourceOperandAst(inst, src2);

            auto node = this->astCtxt->bvshl(
                          op1,
                          this->astCtxt->zx(
                            DWORD_SIZE_BIT-8,
                            this->astCtxt->extract(7, 0, op2)
                          )
                        );
            node1 = this->buildConditionalSemantics(inst, dst, node);
          }

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "LSL(S) operation");

          /* Get condition code node */
          auto cond = node1->getChildren()[0];

          /* Spread taint */
          if (inst.operands.size() == 2) {
            this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1));
          } else {
            auto& src2 = inst.operands[2];

            this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));
          }

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            /* TODO (cnheitman): Implement. */
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


        void Arm32Semantics::lsr_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);

          auto node1 = this->buildConditionalSemantics(inst, dst, op1);

          if (inst.operands.size() == 3) {
            auto& src2 = inst.operands[2];

            auto op2 = this->getArm32SourceOperandAst(inst, src2);

            auto node = this->astCtxt->bvlshr(
                          op1,
                          this->astCtxt->zx(
                            DWORD_SIZE_BIT-8,
                            this->astCtxt->extract(7, 0, op2)
                          )
                        );
            node1 = this->buildConditionalSemantics(inst, dst, node);
          }

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "LSR(S) operation");

          /* Get condition code node */
          auto cond = node1->getChildren()[0];

          /* Spread taint */
          if (inst.operands.size() == 2) {
            this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1));
          } else {
            auto& src2 = inst.operands[2];

            this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));
          }

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            /* TODO (cnheitman): Implement. */
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


        void Arm32Semantics::mov_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node1 = this->getArm32SourceOperandAst(inst, src);
          auto node2 = this->buildConditionalSemantics(inst, dst, node1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "MOV operation");

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
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];
          auto& src2 = inst.operands[2];

          /* Create symbolic operands */
          auto op1 = this->getArm32SourceOperandAst(inst, src1);
          auto op2 = this->getArm32SourceOperandAst(inst, src2);

          /* Create the semantics */
          auto mul   = this->astCtxt->bvmul(
                          this->astCtxt->sx(QWORD_SIZE_BIT, op1),
                          this->astCtxt->sx(QWORD_SIZE_BIT, op2)
                        );
          auto lower = this->astCtxt->extract(DWORD_SIZE_BIT-1, 0, mul);
          auto node1 = this->buildConditionalSemantics(inst, dst, lower);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "MUL(S) operation");

          /* Get condition code node */
          auto cond = node1->getChildren()[0];

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            /* TODO (cnheitman): Implement. */
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Update the symbolic control flow */
          /* TODO (cnheitman):
           *  1. Check PC cannot be as destination register.
           *  2. Refactor controlFlow_s so it doesn't need the dst parameter.
           */
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
            /* TODO (cnheitman): There is an issue here. The manual says that
             * the carry flag should be updated but when we test it against
             * Unicorn it is not update. Bug in UC? Disabling it for now.
             */
            // this->cfAdd_s(inst, cond, expr, dst, op1, op2);
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

          for (unsigned int i = 0; i < inst.operands.size(); i++) {
            auto& dst       = inst.operands[i];
            auto stack      = this->architecture->getStackPointer();
            auto stackValue = this->architecture->getConcreteRegisterValue(stack).convert_to<triton::uint64>();
            auto src        = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue, size));

            /* Create symbolic operands */
            auto op1 = this->symbolicEngine->getOperandAst(inst, dst);
            auto op2 = this->symbolicEngine->getOperandAst(inst, src);

            /* TODO (cnheitman): Improve (refactor?). */
            if (dst.getRegister().getId() == ID_REG_ARM32_PC) {
              op1 = this->clearISSB(op1);
            }

            /* Create the semantics */
            auto node = this->astCtxt->ite(cond, op2, op1);

            /* Create symbolic expression */
            auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "POP operation - Pop register");

            /* Spread taint */
            this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src));

            alignAddStack_s(inst, cond, size);

            /* In case we are poping the PC register do not update the control flow at the end. */
            /* TODO (cnheitman): Better test this. */
            if (cond->evaluate() == true && dst.getRegister().getId() == ID_REG_ARM32_PC) {
              updateControlFlow = false;

              /* Update swtich mode accordingly. */
              this->updateExecutionState(dst, node);
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
          auto cond  = this->getCodeConditionAst(inst);

          for (int i = inst.operands.size()-1; i >= 0; i--) {
            auto& src = inst.operands[i];

            /* Create symbolic operands */
            auto op = this->symbolicEngine->getOperandAst(inst, src);

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
            /* TODO (cnheitman): Implement new version of nf_s and zf_s for this case. */
            // this->nf_s(inst, cond, expr1, dst1);
            // this->zf_s(inst, cond, expr1, dst1);
            /* TODO (cnheitman): Are we check the arch version to update C and V? */
            // this->cfAdd_s(inst, cond, expr1, dst1, op1, op2);
            // this->vfAdd_s(inst, cond, expr1, dst1, op1, op2);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Update the symbolic control flow */
          /* TODO (cnheitman):
           *  1. Check PC cannot be as destination register.
           *  2. Refactor controlFlow_s so it doesn't need the dst1 parameter.
           */
          this->controlFlow_s(inst, cond, dst1);
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
          /* STR <Rt>, [<Rn], #<simm> */
          if (inst.operands.size() == 3) {
            auto& imm = inst.operands[2].getImmediate();
            auto& base = dst.getMemory().getBaseRegister();

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
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "STR operation - Base register computation");

            /* TODO: Fix.*/
            /* Spread taint */
            // this->spreadTaint(inst, cond, expr2, base, this->taintEngine->isTainted(base));
          }

          /* Optional behavior. Pre-indexed computation of the base register. */
          /* STR <Rt>, [<Rn>, #<simm>]! */
          else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
            auto& base = dst.getMemory().getBaseRegister();

            /* Create symbolic operands of the post computation */
            auto baseNode = this->symbolicEngine->getOperandAst(inst, base);

            /* Create the semantics of the base register */
            auto node3 = this->astCtxt->ite(
                            cond,
                            dst.getMemory().getLeaAst(),
                            baseNode
                          );

            /* Create symbolic expression */
            auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "STR operation - Base register computation");

            /* TODO: Fix.*/
            /* Spread taint */
            // this->spreadTaint(inst, cond, expr2, base, this->taintEngine->isTainted(base));
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
          auto cond = this->getCodeConditionAst(inst);
          auto node1 = this->astCtxt->bvand(op1, op2);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "TST operation");

          /* Update symbolic flags */
          /* TODO (cnheitman): UC is not updating the C flag? What is the correct behavior. */
          // this->cfAdd_s(inst, cond, expr, src1, op1, op2
          this->nf_s(inst, cond, expr, src1);
          this->zf_s(inst, cond, expr, src1);

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Update the symbolic control flow */
          this->controlFlow_s(inst);
        }

      }; /* arm32 namespace */
    }; /* arm namespace */
  }; /* arch namespace */
}; /* triton namespace */
