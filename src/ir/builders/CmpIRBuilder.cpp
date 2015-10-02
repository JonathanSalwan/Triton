/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <CmpIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


// Compares the first source operand with the second source operan
// and sets the status flags in the EFLAGS register according to the
// results. The comparison is performed by subtracting the second
// operand from the first operand and then setting the status flags 
// in the same manner as the SUB instruction. When an immediate value
// is used as an operand, it is sign-extended to the length of the
// first operand.


CmpIRBuilder::CmpIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void CmpIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto reg = this->operands[0].getReg();
  auto imm = this->operands[1].getImm().getValue();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  op2 = smt2lib::bv(imm, regSize * REG_SIZE);

  /* Finale expr */
  expr = smt2lib::bvsub(op1, op2);

  /* Create the symbolic expression */
  se = ap.createSE(inst, expr, "Temporary Compare");

  /* Apply the taint */
  ap.assignmentSpreadTaintExprReg(se, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::af(inst, se, ap, regSize, op1, op2);
  EflagsBuilder::cfSub(inst, se, ap, regSize, op1, op2);
  EflagsBuilder::ofSub(inst, se, ap, regSize, op1, op2);
  EflagsBuilder::pf(inst, se, ap, regSize);
  EflagsBuilder::sf(inst, se, ap, regSize);
  EflagsBuilder::zf(inst, se, ap, regSize);
}


void CmpIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto reg1 = this->operands[0].getReg();
  auto reg2 = this->operands[1].getReg();
  auto regSize1 = this->operands[0].getReg().getSize();
  auto regSize2 = this->operands[1].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg1, regSize1);
  op2 = ap.buildSymbolicRegOperand(reg2, regSize2);

  /* Final expr */
  expr = smt2lib::bvsub(op1, op2);

  /* Create the symbolic expression */
  se = ap.createSE(inst, expr, "Temporary Compare");

  /* Apply the taint */
  ap.assignmentSpreadTaintExprRegReg(se, reg1, reg2);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::af(inst, se, ap, regSize1, op1, op2);
  EflagsBuilder::cfSub(inst, se, ap, regSize1, op1, op2);
  EflagsBuilder::ofSub(inst, se, ap, regSize1, op1, op2);
  EflagsBuilder::pf(inst, se, ap, regSize1);
  EflagsBuilder::sf(inst, se, ap, regSize1);
  EflagsBuilder::zf(inst, se, ap, regSize1);
}


void CmpIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto memSize = this->operands[1].getMem().getSize();
  auto mem = this->operands[1].getMem();
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  op2 = ap.buildSymbolicMemOperand(mem, memSize);

  /* Final expr */
  expr = smt2lib::bvsub(op1, op2);

  /* Create the symbolic expression */
  se = ap.createSE(inst, expr);

  /* Apply the taint */
  ap.assignmentSpreadTaintExprRegMem(se, reg, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::af(inst, se, ap, regSize, op1, op2);
  EflagsBuilder::cfSub(inst, se, ap, regSize, op1, op2);
  EflagsBuilder::ofSub(inst, se, ap, regSize, op1, op2);
  EflagsBuilder::pf(inst, se, ap, regSize);
  EflagsBuilder::sf(inst, se, ap, regSize);
  EflagsBuilder::zf(inst, se, ap, regSize);
}


void CmpIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto memSize = this->operands[0].getMem().getSize();
  auto mem = this->operands[0].getMem();
  auto imm = this->operands[1].getImm().getValue();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, memSize);
  op2 = smt2lib::bv(imm, memSize * REG_SIZE);

  /* Final expr */
  expr = smt2lib::bvsub(op1, op2);

  /* Create the symbolic expression */
  se = ap.createSE(inst, expr);

  /* Apply the taint */
  ap.assignmentSpreadTaintExprMem(se, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::af(inst, se, ap, memSize, op1, op2);
  EflagsBuilder::cfSub(inst, se, ap, memSize, op1, op2);
  EflagsBuilder::ofSub(inst, se, ap, memSize, op1, op2);
  EflagsBuilder::pf(inst, se, ap, memSize);
  EflagsBuilder::sf(inst, se, ap, memSize);
  EflagsBuilder::zf(inst, se, ap, memSize);
}


void CmpIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto memSize = this->operands[0].getMem().getSize();
  auto mem = this->operands[0].getMem();
  auto reg = this->operands[1].getReg();
  auto regSize = this->operands[1].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, memSize);
  op2 = ap.buildSymbolicRegOperand(reg, regSize);

  /* Final expr */
  expr = smt2lib::bvsub(op1, op2);

  /* Create the symbolic expression */
  se = ap.createSE(inst, expr);

  /* Apply the taint */
  ap.assignmentSpreadTaintExprRegMem(se, reg, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::af(inst, se, ap, memSize, op1, op2);
  EflagsBuilder::cfSub(inst, se, ap, memSize, op1, op2);
  EflagsBuilder::ofSub(inst, se, ap, memSize, op1, op2);
  EflagsBuilder::pf(inst, se, ap, memSize);
  EflagsBuilder::sf(inst, se, ap, memSize);
  EflagsBuilder::zf(inst, se, ap, memSize);
}


Inst *CmpIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "CMP");
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

