/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <JsIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


JsIRBuilder::JsIRBuilder(reg_size address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void JsIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *sf;
  auto imm = this->operands[0].getImm().getValue();

  /* Create the SMT semantic */
  sf = ap.buildSymbolicFlagOperand(ID_TMP_SF);

  /* Finale expr */
  expr = smt2lib::ite(
            smt2lib::equal(
              sf,
              smt2lib::bvtrue()),
            smt2lib::bv(imm, REG_SIZE_BIT),
            smt2lib::bv(this->nextAddress, REG_SIZE_BIT));

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, ID_TMP_RIP, REG_SIZE, "RIP");

  /* Add the constraint in the PathConstraints list */
  ap.addPathConstraint(se->getID());
}


void JsIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void JsIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void JsIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *JsIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "JS");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

#endif /* LIGHT_VERSION */

