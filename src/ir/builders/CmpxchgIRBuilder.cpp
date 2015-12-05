/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <CmpxchgIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>



CmpxchgIRBuilder::CmpxchgIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void CmpxchgIRBuilder::regImm(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void CmpxchgIRBuilder::regReg(Inst &inst) const {
  SymbolicExpression *se1, *se2, *se3;
  smt2lib::smtAstAbstractNode *expr1, *expr2, *expr3, *rax, *op1, *op2;
  auto reg1 = this->operands[0].getReg();
  auto reg2 = this->operands[1].getReg();
  auto regSize1 = this->operands[0].getReg().getSize();
  auto regSize2 = this->operands[1].getReg().getSize();

  /* Create the SMT semantic */
  rax = ap.buildSymbolicRegOperand(ID_TMP_RAX, regSize1);
  op1 = ap.buildSymbolicRegOperand(reg1, regSize1);
  op2 = ap.buildSymbolicRegOperand(reg2, regSize2);

  /* Cmp expr */
  expr1 = smt2lib::bvsub(rax, op1);

  /* xchg expr */
  expr2 = smt2lib::ite(
            smt2lib::equal(rax, op1),
            op2,
            op1);

  expr3 = smt2lib::ite(
            smt2lib::equal(rax, op1),
            rax,
            op1);

  /* Create the symbolic expression */
  se1 = ap.createSE(inst, expr1, "Temporary Compare");
  se2 = ap.createRegSE(inst, expr2, reg1, regSize1);
  se3 = ap.createRegSE(inst, expr3, ID_TMP_RAX, regSize1);

  /* Apply the taint */
  ap.assignmentSpreadTaintExprRegReg(se1, ID_TMP_RAX, reg1);
  ap.assignmentSpreadTaintRegReg(se2, reg1, reg2);
  ap.assignmentSpreadTaintRegReg(se3, ID_TMP_RAX, reg1);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::af(inst, se1, reg1, rax, op1);
  EflagsBuilder::cfSub(inst, se1, reg1, rax, op1);
  EflagsBuilder::ofSub(inst, se1, reg1, rax, op1);
  EflagsBuilder::pf(inst, se1, reg1);
  EflagsBuilder::sf(inst, se1, reg1);
  EflagsBuilder::zf(inst, se1, reg1);
}


void CmpxchgIRBuilder::regMem(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void CmpxchgIRBuilder::memImm(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void CmpxchgIRBuilder::memReg(Inst &inst) const {
  SymbolicExpression *se1, *se2, *se3;
  smt2lib::smtAstAbstractNode *expr1, *expr2, *expr3, *rax, *op1, *op2;
  auto memSize = this->operands[0].getMem().getSize();
  auto mem = this->operands[0].getMem();
  auto reg = this->operands[1].getReg();
  auto regSize = this->operands[1].getReg().getSize();

  /* Create the SMT semantic */
  rax = ap.buildSymbolicRegOperand(ID_TMP_RAX, memSize);
  op1 = ap.buildSymbolicMemOperand(mem, memSize);
  op2 = ap.buildSymbolicRegOperand(reg, regSize);

  /* Cmp expr */
  expr1 = smt2lib::bvsub(rax, op1);

  /* xchg expr */
  expr2 = smt2lib::ite(
            smt2lib::equal(rax, op1),
            op2,
            op1);

  expr3 = smt2lib::ite(
            smt2lib::equal(rax, op1),
            rax,
            op1);

  /* Create the symbolic expression */
  se1 = ap.createSE(inst, expr1, "Temporary Compare");
  se2 = ap.createMemSE(inst, expr2, mem, memSize);
  se3 = ap.createRegSE(inst, expr3, ID_TMP_RAX, memSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintExprRegMem(se1, ID_TMP_RAX, mem, memSize);
  ap.assignmentSpreadTaintMemReg(se2, mem, reg, memSize);
  ap.assignmentSpreadTaintRegMem(se3, ID_TMP_RAX, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::af(inst, se1, mem, rax, op1);
  EflagsBuilder::cfSub(inst, se1, mem, rax, op1);
  EflagsBuilder::ofSub(inst, se1, mem, rax, op1);
  EflagsBuilder::pf(inst, se1, mem);
  EflagsBuilder::sf(inst, se1, mem);
  EflagsBuilder::zf(inst, se1, mem);
}


Inst *CmpxchgIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "CMPXCHG");
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

