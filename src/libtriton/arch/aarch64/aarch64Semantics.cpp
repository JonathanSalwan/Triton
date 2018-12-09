//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/aarch64Semantics.hpp>
#include <triton/aarch64Specifications.hpp>
#include <triton/astContext.hpp>
#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>



/*! \page SMT_aarch64_Semantics_Supported_page AArch64 SMT semantics supported
    \brief [**internal**] List of the supported semantics for the AArch64 architecture.


Mnemonic                     | Description
-----------------------------|------------
ADC                          | Add with Carry
ADD (extended register)      | Add (extended register)
ADD (immediate)              | Add (immediate)
ADD (shifted register)       | Add (shifted register)
ADR                          | Form PC-relative address
ADRP                         | Form PC-relative address to 4KB page
AND (immediate)              | Bitwise AND (immediate).
AND (shifted register)       | Bitwise AND (shifted register).
ASR (immediate)              | Arithmetic Shift Right (immediate): an alias of SBFM
ASR (register)               | Arithmetic Shift Right (register): an alias of ASRV
EOR (immediate)              | Bitwise Exclusive OR (immediate).
EOR (shifted register)       | Bitwise Exclusive OR (shifted register).
MOVZ                         | Move shifted 16-bit immediate to register
SUB (extended register)      | Subtract (extended register).
SUB (immediate)              | Subtract (immediate).
SUB (shifted register)       | Subtract (shifted register).

*/


namespace triton {
  namespace arch {
    namespace aarch64 {

      AArch64Semantics::AArch64Semantics(triton::arch::Architecture* architecture,
                                         triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                                         triton::engines::taint::TaintEngine* taintEngine,
                                         triton::ast::AstContext& astCtxt) : astCtxt(astCtxt) {

        this->architecture    = architecture;
        this->symbolicEngine  = symbolicEngine;
        this->taintEngine     = taintEngine;

        if (architecture == nullptr)
          throw triton::exceptions::Semantics("AArch64Semantics::AArch64Semantics(): The architecture API must be defined.");

        if (this->symbolicEngine == nullptr)
          throw triton::exceptions::Semantics("AArch64Semantics::AArch64Semantics(): The symbolic engine API must be defined.");

        if (this->taintEngine == nullptr)
          throw triton::exceptions::Semantics("AArch64Semantics::AArch64Semantics(): The taint engines API must be defined.");
      }


      bool AArch64Semantics::buildSemantics(triton::arch::Instruction& inst) {
        switch (inst.getType()) {
          case ID_INS_ADC:       this->adc_s(inst);           break;
          case ID_INS_ADD:       this->add_s(inst);           break;
          case ID_INS_ADR:       this->adr_s(inst);           break;
          case ID_INS_ADRP:      this->adrp_s(inst);          break;
          case ID_INS_AND:       this->and_s(inst);           break;
          case ID_INS_ASR:       this->asr_s(inst);           break;
          case ID_INS_EOR:       this->eor_s(inst);           break;
          case ID_INS_MOVZ:      this->movz_s(inst);          break;
          case ID_INS_SUB:       this->sub_s(inst);           break;
          default:
            return false;
        }
        return true;
      }


      void AArch64Semantics::controlFlow_s(triton::arch::Instruction& inst) {
        auto pc = triton::arch::OperandWrapper(this->architecture->getParentRegister(ID_REG_AARCH64_PC));

        /* Create the semantics */
        auto node = this->astCtxt.bv(inst.getNextAddress(), pc.getBitSize());

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicRegisterExpression(inst, node, this->architecture->getParentRegister(ID_REG_AARCH64_PC), "Program Counter");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaintRegister(this->architecture->getParentRegister(ID_REG_AARCH64_PC), triton::engines::taint::UNTAINTED);
      }


      void AArch64Semantics::adc_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto  cf   = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_C));

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);
        auto op3 = this->symbolicEngine->getOperandAst(inst, cf);

        /* Create the semantics */
        auto node = this->astCtxt.bvadd(this->astCtxt.bvadd(op1, op2), this->astCtxt.zx(dst.getBitSize()-1, op3));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ADC operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(cf));

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::add_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvadd(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ADD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::adr_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  pc  = triton::arch::OperandWrapper(this->architecture->getParentRegister(ID_REG_AARCH64_PC));

        /*
         * Note: Capstone already encodes the result into the source operand. We don't have
         * to compute the add operation but do we lose the symbolic?
         */
        /* Create symbolic semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ADR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src) | this->taintEngine->isTainted(pc));

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::adrp_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  pc  = triton::arch::OperandWrapper(this->architecture->getParentRegister(ID_REG_AARCH64_PC));

        /*
         * Note: Capstone already encodes the result into the source operand. We don't have
         * to compute the add operation but do we lose the symbolic?
         */
        /* Create symbolic semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ADRP operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src) | this->taintEngine->isTainted(pc));

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::and_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvand(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "AND operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::asr_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvashr(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ASR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::eor_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvxor(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "EOR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::movz_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVZ operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::sub_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvsub(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SUB operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }

    }; /* aarch64 namespace */
  }; /* arch namespace */
}; /* triton namespace */
