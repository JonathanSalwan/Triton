/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <algorithm>
#include <sstream>
#include <stdexcept>
#include <list>

#include <PmovmskbIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


PmovmskbIRBuilder::PmovmskbIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void PmovmskbIRBuilder::regImm(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void PmovmskbIRBuilder::regReg(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op2;
  std::list<smt2lib::smtAstAbstractNode *> mskb;
  auto reg1 = this->operands[0].getReg();
  auto regSize1 = this->operands[0].getReg().getSize();
  auto reg2 = this->operands[1].getReg();
  auto regSize2 = this->operands[1].getReg().getSize();

  /* PIN_GetContextReg doesn't supports MMX registers. */
  /* In this case, we skip the IR processing. */
  if (!reg2.isValid())
    return;

  op2 = ap.buildSymbolicRegOperand(reg2, regSize2);

  mskb.push_back(smt2lib::extract(127, 127, op2));
  mskb.push_back(smt2lib::extract(119, 119, op2));
  mskb.push_back(smt2lib::extract(111, 111, op2));
  mskb.push_back(smt2lib::extract(103, 103, op2));
  mskb.push_back(smt2lib::extract(95,  95,  op2));
  mskb.push_back(smt2lib::extract(87,  87,  op2));
  mskb.push_back(smt2lib::extract(79,  79,  op2));
  mskb.push_back(smt2lib::extract(71,  71,  op2));
  mskb.push_back(smt2lib::extract(63,  63,  op2));
  mskb.push_back(smt2lib::extract(55,  55,  op2));
  mskb.push_back(smt2lib::extract(47,  47,  op2));
  mskb.push_back(smt2lib::extract(39,  39,  op2));
  mskb.push_back(smt2lib::extract(31,  31,  op2));
  mskb.push_back(smt2lib::extract(23,  23,  op2));
  mskb.push_back(smt2lib::extract(15,  15,  op2));
  mskb.push_back(smt2lib::extract(7,   7,   op2));

  /* Create the SMT semantic */
  expr = smt2lib::zx(16, smt2lib::concat(mskb));

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg1, regSize1);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegReg(se, reg1, reg2);
}


void PmovmskbIRBuilder::regMem(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void PmovmskbIRBuilder::memImm(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void PmovmskbIRBuilder::memReg(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *PmovmskbIRBuilder::process(void) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "PMOVMSKB");
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

