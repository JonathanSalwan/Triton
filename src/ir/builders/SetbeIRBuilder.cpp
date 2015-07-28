/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <SetbeIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


SetbeIRBuilder::SetbeIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void SetbeIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void SetbeIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *cf, *zf;
  uint64 reg     = this->operands[0].getValue();
  uint64 regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  cf = ap.buildSymbolicFlagOperand(ID_CF);
  zf = ap.buildSymbolicFlagOperand(ID_ZF);

  /* Finale expr */
  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvor(
                cf,
                zf
              ),
              smt2lib::bvtrue()),
            smt2lib::bv(1, BYTE_SIZE_BIT),
            smt2lib::bv(0, BYTE_SIZE_BIT));

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_CF) | ap.getFlagValue(ID_ZF)) {
    if (ap.isRegTainted(ID_CF) == TAINTED)
      ap.assignmentSpreadTaintRegReg(se, reg, ID_CF);
    else
      ap.assignmentSpreadTaintRegReg(se, reg, ID_ZF);
  }

}


void SetbeIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *cf, *zf;
  uint64 mem     = this->operands[0].getValue();
  uint64 memSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  cf = ap.buildSymbolicFlagOperand(ID_CF);
  zf = ap.buildSymbolicFlagOperand(ID_ZF);

  /* Finale expr */
  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvor(
                cf,
                zf
              ),
              smt2lib::bvtrue()),
            smt2lib::bv(1, BYTE_SIZE_BIT),
            smt2lib::bv(0, BYTE_SIZE_BIT));

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_CF) | ap.getFlagValue(ID_ZF)) {
    if (ap.isRegTainted(ID_CF) == TAINTED)
      ap.assignmentSpreadTaintMemReg(se, mem, ID_CF, memSize);
    else
      ap.assignmentSpreadTaintMemReg(se, mem, ID_ZF, memSize);
  }

}


void SetbeIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *SetbeIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "SETBE");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

