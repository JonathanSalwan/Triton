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


CmpIRBuilder::CmpIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void CmpIRBuilder::regImm(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto reg = this->operands[0].getReg();
  auto imm = this->operands[1].getImm().getValue();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  op2 = smt2lib::bv(imm, regSize * BYTE_SIZE_BIT);

  /* Finale expr */
  expr = smt2lib::bvsub(op1, op2);

  /* Create the symbolic expression */
  se = ap.createSE(inst, expr, "Temporary Compare");

  /* Apply the taint */
  ap.assignmentSpreadTaintExprReg(se, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::af(inst, se, reg, op1, op2);
  EflagsBuilder::cfSub(inst, se, reg, op1, op2);
  EflagsBuilder::ofSub(inst, se, reg, op1, op2);
  EflagsBuilder::pf(inst, se, reg);
  EflagsBuilder::sf(inst, se, reg);
  EflagsBuilder::zf(inst, se, reg);
}


void CmpIRBuilder::regReg(Inst &inst) const {
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
  EflagsBuilder::af(inst, se, reg1, op1, op2);
  EflagsBuilder::cfSub(inst, se, reg1, op1, op2);
  EflagsBuilder::ofSub(inst, se, reg1, op1, op2);
  EflagsBuilder::pf(inst, se, reg1);
  EflagsBuilder::sf(inst, se, reg1);
  EflagsBuilder::zf(inst, se, reg1);
}


void CmpIRBuilder::regMem(Inst &inst) const {
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
  EflagsBuilder::af(inst, se, reg, op1, op2);
  EflagsBuilder::cfSub(inst, se, reg, op1, op2);
  EflagsBuilder::ofSub(inst, se, reg, op1, op2);
  EflagsBuilder::pf(inst, se, reg);
  EflagsBuilder::sf(inst, se, reg);
  EflagsBuilder::zf(inst, se, reg);
}


void CmpIRBuilder::memImm(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto memSize = this->operands[0].getMem().getSize();
  auto mem = this->operands[0].getMem();
  auto imm = this->operands[1].getImm().getValue();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, memSize);
  op2 = smt2lib::bv(imm, memSize * BYTE_SIZE_BIT);

  /* Final expr */
  expr = smt2lib::bvsub(op1, op2);

  /* Create the symbolic expression */
  se = ap.createSE(inst, expr);

  /* Apply the taint */
  ap.assignmentSpreadTaintExprMem(se, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::af(inst, se, mem, op1, op2);
  EflagsBuilder::cfSub(inst, se, mem, op1, op2);
  EflagsBuilder::ofSub(inst, se, mem, op1, op2);
  EflagsBuilder::pf(inst, se, mem);
  EflagsBuilder::sf(inst, se, mem);
  EflagsBuilder::zf(inst, se, mem);
}


void CmpIRBuilder::memReg(Inst &inst) const {
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
  EflagsBuilder::af(inst, se, mem, op1, op2);
  EflagsBuilder::cfSub(inst, se, mem, op1, op2);
  EflagsBuilder::ofSub(inst, se, mem, op1, op2);
  EflagsBuilder::pf(inst, se, mem);
  EflagsBuilder::sf(inst, se, mem);
  EflagsBuilder::zf(inst, se, mem);
}


Inst *CmpIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "CMP");
    ControlFlow::rip(*inst, this->nextAddress);
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

#endif /* LIGHT_VERSION */

