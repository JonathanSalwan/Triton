/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <RetIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


RetIRBuilder::RetIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


static SymbolicExpression *alignStack(Inst &inst, AnalysisProcessor &ap)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(ID_RSP, REG_SIZE);
  op2 = smt2lib::bv(REG_SIZE, REG_SIZE_BIT);

  expr = smt2lib::bvadd(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, ID_RSP, REG_SIZE, "Aligns stack");

  /* Apply the taint */
  se->isTainted = ap.isRegTainted(ID_RSP);

  return se;
}


static SymbolicExpression *alignStack(Inst &inst, AnalysisProcessor &ap, uint64 imm)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(ID_RSP, REG_SIZE);
  op2 = smt2lib::bv(imm, REG_SIZE_BIT);

  expr = smt2lib::bvadd(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, ID_RSP, REG_SIZE, "Aligns stack");

  /* Apply the taint */
  se->isTainted = ap.isRegTainted(ID_RSP);

  return se;
}


void RetIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no 'ret reg' in x86 */
  OneOperandTemplate::stop(this->disas);
}


void RetIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1;
  uint64 imm       = this->operands[0].getValue();
  uint64 memSrc    = this->operands[1].getValue(); // The dst memory read
  uint32 readSize  = this->operands[1].getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(memSrc, readSize);

  /* Finale expr */
  expr = op1;

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, ID_RIP, REG_SIZE, "RIP");

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se, ID_RIP, memSrc, readSize);

  /* Create the SMT semantic side effect */
  alignStack(inst, ap);
  alignStack(inst, ap, imm);
}


void RetIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1;
  uint64 memSrc    = this->operands[0].getValue(); // The dst memory read
  uint32 readSize  = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(memSrc, readSize);

  /* Finale expr */
  expr = op1;

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, ID_RIP, REG_SIZE, "RIP");

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se, ID_RIP, memSrc, readSize);

  /* Create the SMT semantic side effect */
  alignStack(inst, ap);
}


void RetIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  /* The ret instruction without argument is in the RetIRBuilder::mem function. */
  /* As ret has an implicit read memory (saved EIP), it contains at least one memory argument. */
  OneOperandTemplate::stop(this->disas);
}


Inst *RetIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "RET");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

