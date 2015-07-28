/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <CqoIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


CqoIRBuilder::CqoIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void CqoIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se1, *se3;
  smt2lib::smtAstAbstractNode *expr1, *expr2, *expr3, *op1;

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(ID_RAX, REG_SIZE, 63, 0);

  /* Expression 1: TMP = 128 bitvec (RDX:RAX) */
  expr1 = smt2lib::sx(64, op1);
  se1 = ap.createSE(inst, expr1, "Temporary variable");

  /* Expression 2: RAX = TMP[63...0] */
  expr2 = smt2lib::extract(63, 0, smt2lib::reference(se1->getID()));
  ap.createRegSE(inst, expr2, ID_RAX, REG_SIZE, "RAX");

  /* Expression 3: RDX = TMP[127...64] */
  expr3 = smt2lib::extract(127, 64, smt2lib::reference(se1->getID()));
  se3 = ap.createRegSE(inst, expr3, ID_RDX, REG_SIZE, "RDX");

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se3, ID_RDX, ID_RAX);
}


Inst *CqoIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "CQO");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

