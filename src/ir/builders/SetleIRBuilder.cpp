/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <SetleIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


SetleIRBuilder::SetleIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void SetleIRBuilder::imm(Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void SetleIRBuilder::reg(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *sf, *of, *zf;
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the flag SMT semantic */
  sf = ap.buildSymbolicFlagOperand(ID_TMP_SF);
  of = ap.buildSymbolicFlagOperand(ID_TMP_OF);
  zf = ap.buildSymbolicFlagOperand(ID_TMP_ZF);

  /* Finale expr */
  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvor(smt2lib::bvxor(sf, of), zf),
              smt2lib::bvtrue()),
            smt2lib::bv(1, BYTE_SIZE_BIT),
            smt2lib::bv(0, BYTE_SIZE_BIT));

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint via the concretization */
  if (((ap.getFlagValue(ID_TMP_SF) ^ ap.getFlagValue(ID_TMP_OF)) | ap.getFlagValue(ID_TMP_ZF)) == 1) {
    if (ap.isRegTainted(ID_TMP_SF) == TAINTED)
      ap.assignmentSpreadTaintRegReg(se, reg, ID_TMP_SF);
    else if (ap.isRegTainted(ID_TMP_OF) == TAINTED)
      ap.assignmentSpreadTaintRegReg(se, reg, ID_TMP_OF);
    else
      ap.assignmentSpreadTaintRegReg(se, reg, ID_TMP_ZF);
  }

}


void SetleIRBuilder::mem(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *sf, *of, *zf;
  auto mem = this->operands[0].getMem();
  auto memSize = this->operands[0].getMem().getSize();

  /* Create the flag SMT semantic */
  sf = ap.buildSymbolicFlagOperand(ID_TMP_SF);
  of = ap.buildSymbolicFlagOperand(ID_TMP_OF);
  zf = ap.buildSymbolicFlagOperand(ID_TMP_ZF);

  /* Finale expr */
  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvor(smt2lib::bvxor(sf, of), zf),
              smt2lib::bvtrue()),
            smt2lib::bv(1, BYTE_SIZE_BIT),
            smt2lib::bv(0, BYTE_SIZE_BIT));

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint via the concretization */
  if (((ap.getFlagValue(ID_TMP_SF) ^ ap.getFlagValue(ID_TMP_OF)) | ap.getFlagValue(ID_TMP_ZF)) == 1) {
    if (ap.isRegTainted(ID_TMP_SF) == TAINTED)
      ap.assignmentSpreadTaintMemReg(se, mem, ID_TMP_SF, memSize);
    else if (ap.isRegTainted(ID_TMP_OF) == TAINTED)
      ap.assignmentSpreadTaintMemReg(se, mem, ID_TMP_OF, memSize);
    else
      ap.assignmentSpreadTaintMemReg(se, mem, ID_TMP_ZF, memSize);
  }

}


void SetleIRBuilder::none(Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *SetleIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "SETLE");
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

