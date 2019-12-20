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
BX                            | Branch and Exchange

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
            case ID_INS_BX:        this->bx_s(inst);            break;
            default:
              return false;
          }
          return true;
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
          if (cond->evaluate() == true && inst.isUpdateFlag() == false && dst.getRegister().getId() == ID_REG_ARM32_PC) {
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


        void Arm32Semantics::adc_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];
          auto& src2 = inst.operands[2];
          auto  cf   = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_C));

          /* Create symbolic operands */
          auto op1 = this->symbolicEngine->getOperandAst(inst, dst);
          auto op2 = this->symbolicEngine->getOperandAst(inst, src1);
          auto op3 = this->symbolicEngine->getOperandAst(inst, src2);
          auto op4 = this->symbolicEngine->getOperandAst(inst, cf);

          /* Create the semantics */
          auto cond  = this->getCodeConditionAst(inst);
          auto node1 = this->astCtxt->bvadd(
                          this->astCtxt->bvadd(op2, op3),
                          this->astCtxt->zx(dst.getBitSize()-1, op4)
                        );
          auto node2 = this->astCtxt->ite(cond, node1, op1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "ADC(S) operation");

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(cf));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->cfAdd_s(inst, cond, expr, dst, op2, op3);
            this->nf_s(inst, cond, expr, dst);
            this->vfAdd_s(inst, cond, expr, dst, op2, op3);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Update the symbolic control flow */
          /* TODO (cnheitman): Not clear what to do when S == 1 and Rd == PC. Test. */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::add_s(triton::arch::Instruction& inst) {
          /* TODO (cnheitman): In ARM mode, PC can be used as the destination register. Implement. */

          auto& dst  = inst.operands[0];
          auto& src1 = inst.operands[1];
          auto& src2 = inst.operands[2];

          /* Create symbolic operands */
          auto op1 = this->symbolicEngine->getOperandAst(inst, dst);
          auto op2 = this->symbolicEngine->getOperandAst(inst, src1);
          auto op3 = this->symbolicEngine->getOperandAst(inst, src2);

          /* Create the semantics */
          auto cond  = this->getCodeConditionAst(inst);
          auto node1 = this->astCtxt->bvadd(op2, op3);
          auto node2 = this->astCtxt->ite(cond, node1, op1);

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "ADD(S) operation");

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

          /* Update symbolic flags */
          if (inst.isUpdateFlag() == true) {
            this->cfAdd_s(inst, cond, expr, dst, op2, op3);
            this->nf_s(inst, cond, expr, dst);
            this->vfAdd_s(inst, cond, expr, dst, op2, op3);
            this->zf_s(inst, cond, expr, dst);
          }

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);
          }

          /* Update the symbolic control flow */
          /* TODO (cnheitman): Not clear what to do when S == 1 and Rd == PC. Test. */
          this->controlFlow_s(inst, cond, dst);
        }


        void Arm32Semantics::bx_s(triton::arch::Instruction& inst) {
          auto  dst = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_ARM32_PC));
          auto& src = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = this->symbolicEngine->getOperandAst(inst, src);
          auto op2 = this->astCtxt->bv(inst.getNextAddress(), dst.getBitSize());

          /* Create the semantics */
          auto cond  = this->getCodeConditionAst(inst);
          auto node1 = this->astCtxt->ite(
                          cond,
                          this->astCtxt->bvand(
                            op1,
                            this->astCtxt->bv(op1->getBitvectorMask()-1, src.getBitSize())
                          ),  /* Set instruction set selection bit to 0. */
                          op2
                        );

          /* Create symbolic expression */
          auto expr = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "BX operation - Program Counter");

          /* Spread taint */
          this->spreadTaint(inst, cond, expr, dst, this->getCodeConditionTaintState(inst));

          /* Update condition flag */
          if (cond->evaluate() == true) {
            inst.setConditionTaken(true);

            /* Check instruction set selection bit and set mode accordingly. */
            auto cpu = static_cast<triton::arch::arm::arm32::Arm32Cpu*>(this->architecture->getCpuInstance());
            auto isb = op1->evaluate() & 0x1;
            cpu->setThumb(isb == 0x1);
          }

          /* Create the path constraint */
          this->symbolicEngine->pushPathConstraint(inst, expr);
        }

      }; /* arm32 namespace */
    }; /* arm namespace */
  }; /* arch namespace */
}; /* triton namespace */
