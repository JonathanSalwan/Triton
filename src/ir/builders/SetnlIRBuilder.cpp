/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <SetnlIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


SetnlIRBuilder::SetnlIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void SetnlIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void SetnlIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *sf, *of;
  uint64 reg     = this->operands[0].getValue();
  uint64 regSize = this->operands[0].getSize();

  /* Create the flag SMT semantic */
  sf = ap.buildSymbolicFlagOperand(ID_SF);
  of = ap.buildSymbolicFlagOperand(ID_OF);

  /* Finale expr */
  expr = smt2lib::ite(
            smt2lib::equal(
              sf,
              of
            ),
            smt2lib::bv(1, BYTE_SIZE_BIT),
            smt2lib::bv(0, BYTE_SIZE_BIT));

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_SF) == ap.getFlagValue(ID_OF)) {
    if (ap.isRegTainted(ID_SF) == TAINTED)
      ap.assignmentSpreadTaintRegReg(se, reg, ID_SF);
    else
      ap.assignmentSpreadTaintRegReg(se, reg, ID_OF);
  }

}


void SetnlIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *sf, *of;
  uint64 mem     = this->operands[0].getValue();
  uint64 memSize = this->operands[0].getSize();

  /* Create the flag SMT semantic */
  sf = ap.buildSymbolicFlagOperand(ID_SF);
  of = ap.buildSymbolicFlagOperand(ID_OF);

  /* Finale expr */
  expr = smt2lib::ite(
            smt2lib::equal(
              sf,
              of
            ),
            smt2lib::bv(1, BYTE_SIZE_BIT),
            smt2lib::bv(0, BYTE_SIZE_BIT));

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_SF) == ap.getFlagValue(ID_OF)) {
    if (ap.isRegTainted(ID_SF) == TAINTED)
      ap.assignmentSpreadTaintMemReg(se, mem, ID_SF, memSize);
    else
      ap.assignmentSpreadTaintMemReg(se, mem, ID_OF, memSize);
  }

}


void SetnlIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *SetnlIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "SETNL");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

