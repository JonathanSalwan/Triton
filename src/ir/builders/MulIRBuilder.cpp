/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <MulIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


MulIRBuilder::MulIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void MulIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2, *rax, *rdx;
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(ID_TMP_RAX, regSize);
  op2 = ap.buildSymbolicRegOperand(reg, regSize);

  switch (regSize) {

    /* AX = AL * r/m8 */
    case BYTE_SIZE:
      /* Final expr */
      expr = smt2lib::bvmul(
                smt2lib::zx(BYTE_SIZE_BIT, op1),
                smt2lib::zx(BYTE_SIZE_BIT, op2)
              );
      /* Create the symbolic expression */
      se = ap.createRegSE(inst, expr, ID_TMP_RAX, WORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegReg(se, ID_TMP_RAX, reg);
      /* Add the symbolic flags expression to the current inst */
      rax = smt2lib::extract(15, 8, expr);
      EflagsBuilder::cfMul(inst, se, ap, regSize, rax);
      EflagsBuilder::ofMul(inst, se, ap, regSize, rax);
      break;

    /* DX:AX = AX * r/m16 */
    case WORD_SIZE:
      /* Final expr */
      expr = smt2lib::bvmul(
                smt2lib::zx(WORD_SIZE_BIT, op1),
                smt2lib::zx(WORD_SIZE_BIT, op2)
              );
      rax = smt2lib::extract(15, 0, expr);
      rdx = smt2lib::extract(31, 16, expr);
      /* Create the symbolic expression for AX */
      se = ap.createRegSE(inst, rax, ID_TMP_RAX, WORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegReg(se, ID_TMP_RAX, reg);
      /* Create the symbolic expression for DX */
      se = ap.createRegSE(inst, rdx, ID_TMP_RDX, WORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegReg(se, ID_TMP_RDX, reg);
      /* Add the symbolic flags expression to the current inst */
      EflagsBuilder::cfMul(inst, se, ap, regSize, rdx);
      EflagsBuilder::ofMul(inst, se, ap, regSize, rdx);
      break;

    /* EDX:EAX = EAX * r/m32 */
    case DWORD_SIZE:
      /* Final expr */
      expr = smt2lib::bvmul(
                smt2lib::zx(DWORD_SIZE_BIT, op1),
                smt2lib::zx(DWORD_SIZE_BIT, op2)
              );
      rax = smt2lib::extract(31, 0, expr);
      rdx = smt2lib::extract(63, 32, expr);
      /* Create the symbolic expression for EAX */
      se = ap.createRegSE(inst, rax, ID_TMP_RAX, DWORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegReg(se, ID_TMP_RAX, reg);
      /* Create the symbolic expression for EDX */
      se = ap.createRegSE(inst, rdx, ID_TMP_RDX, DWORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegReg(se, ID_TMP_RDX, reg);
      /* Add the symbolic flags expression to the current inst */
      EflagsBuilder::cfMul(inst, se, ap, regSize, rdx);
      EflagsBuilder::ofMul(inst, se, ap, regSize, rdx);
      break;

    /* RDX:RAX = RAX * r/m64 */
    case QWORD_SIZE:
      /* Final expr */
      expr = smt2lib::bvmul(
                smt2lib::zx(QWORD_SIZE_BIT, op1),
                smt2lib::zx(QWORD_SIZE_BIT, op2)
              );
      rax = smt2lib::extract(63, 0, expr);
      rdx = smt2lib::extract(127, 64, expr);
      /* Create the symbolic expression for RAX */
      se = ap.createRegSE(inst, rax, ID_TMP_RAX, QWORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegReg(se, ID_TMP_RAX, reg);
      /* Create the symbolic expression for RDX */
      se = ap.createRegSE(inst, rdx, ID_TMP_RDX, QWORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegReg(se, ID_TMP_RDX, reg);
      /* Add the symbolic flags expression to the current inst */
      EflagsBuilder::cfMul(inst, se, ap, regSize, rdx);
      EflagsBuilder::ofMul(inst, se, ap, regSize, rdx);
      break;

  }

}


void MulIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2, *rax, *rdx;
  auto mem = this->operands[0].getMem();
  auto memSize = this->operands[0].getMem().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(ID_TMP_RAX, memSize);
  op2 = ap.buildSymbolicMemOperand(mem, memSize);

  switch (memSize) {

    /* AX = AL * r/m8 */
    case BYTE_SIZE:
      /* Final expr */
      expr = smt2lib::bvmul(
                smt2lib::zx(BYTE_SIZE_BIT, op1),
                smt2lib::zx(BYTE_SIZE_BIT, op2)
              );
      /* Create the symbolic expression */
      se = ap.createRegSE(inst, expr, ID_TMP_RAX, WORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegMem(se, ID_TMP_RAX, mem, memSize);
      /* Add the symbolic flags expression to the current inst */
      rax = smt2lib::extract(15, 8, expr);
      EflagsBuilder::cfMul(inst, se, ap, memSize, rax);
      EflagsBuilder::ofMul(inst, se, ap, memSize, rax);
      break;

    /* DX:AX = AX * r/m16 */
    case WORD_SIZE:
      /* Final expr */
      expr = smt2lib::bvmul(
                smt2lib::zx(WORD_SIZE_BIT, op1),
                smt2lib::zx(WORD_SIZE_BIT, op2)
              );
      rax = smt2lib::extract(15, 0, expr);
      rdx = smt2lib::extract(31, 16, expr);
      /* Create the symbolic expression for AX */
      se = ap.createRegSE(inst, rax, ID_TMP_RAX, WORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegMem(se, ID_TMP_RAX, mem, memSize);
      /* Create the symbolic expression for DX */
      se = ap.createRegSE(inst, rdx, ID_TMP_RDX, WORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegMem(se, ID_TMP_RDX, mem, memSize);
      /* Add the symbolic flags expression to the current inst */
      EflagsBuilder::cfMul(inst, se, ap, memSize, rdx);
      EflagsBuilder::ofMul(inst, se, ap, memSize, rdx);
      break;

    /* EDX:EAX = EAX * r/m32 */
    case DWORD_SIZE:
      /* Final expr */
      expr = smt2lib::bvmul(
                smt2lib::zx(DWORD_SIZE_BIT, op1),
                smt2lib::zx(DWORD_SIZE_BIT, op2)
              );
      rax = smt2lib::extract(31, 0, expr);
      rdx = smt2lib::extract(63, 32, expr);
      /* Create the symbolic expression for EAX */
      se = ap.createRegSE(inst, rax, ID_TMP_RAX, DWORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegMem(se, ID_TMP_RAX, mem, memSize);
      /* Create the symbolic expression for EDX */
      se = ap.createRegSE(inst, rdx, ID_TMP_RDX, DWORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegMem(se, ID_TMP_RDX, mem, memSize);
      /* Add the symbolic flags expression to the current inst */
      EflagsBuilder::cfMul(inst, se, ap, memSize, rdx);
      EflagsBuilder::ofMul(inst, se, ap, memSize, rdx);
      break;

    /* RDX:RAX = RAX * r/m64 */
    case QWORD_SIZE:
      /* Final expr */
      expr = smt2lib::bvmul(
                smt2lib::zx(QWORD_SIZE_BIT, op1),
                smt2lib::zx(QWORD_SIZE_BIT, op2)
              );
      rax = smt2lib::extract(63, 0, expr);
      rdx = smt2lib::extract(127, 64, expr);
      /* Create the symbolic expression for RAX */
      se = ap.createRegSE(inst, rax, ID_TMP_RAX, QWORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegMem(se, ID_TMP_RAX, mem, memSize);
      /* Create the symbolic expression for RDX */
      se = ap.createRegSE(inst, rdx, ID_TMP_RDX, QWORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegMem(se, ID_TMP_RDX, mem, memSize);
      /* Add the symbolic flags expression to the current inst */
      EflagsBuilder::cfMul(inst, se, ap, memSize, rdx);
      EflagsBuilder::ofMul(inst, se, ap, memSize, rdx);
      break;

  }

}


void MulIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <inc imm> available in x86 */
  OneOperandTemplate::stop(this->disas);
}


void MulIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <inc none> available in x86 */
  OneOperandTemplate::stop(this->disas);
}


Inst *MulIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "MUL");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

#endif /* LIGHT_VERSION */

