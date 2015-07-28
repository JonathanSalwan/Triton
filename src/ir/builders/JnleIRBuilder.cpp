/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <JnleIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


JnleIRBuilder::JnleIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void JnleIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *sf, *of, *zf;
  uint64 imm   = this->operands[0].getValue();

  /* Create the SMT semantic */
  sf = ap.buildSymbolicFlagOperand(ID_SF);
  of = ap.buildSymbolicFlagOperand(ID_OF);
  zf = ap.buildSymbolicFlagOperand(ID_ZF);

  /* 
   * Finale expr
   * JNLE: Jump if not less or equal ((SF^OF | ZF) == 0).
   * SMT: (= (bvor (bvxor sf of) zf) FALSE)
   */
  expr = smt2lib::ite(
            smt2lib::equal(
                smt2lib::bvor(smt2lib::bvxor(sf, of), zf),
                smt2lib::bvfalse()
            ),
            smt2lib::bv(imm, REG_SIZE_BIT),
            smt2lib::bv(this->nextAddress, REG_SIZE_BIT));

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, ID_RIP, REG_SIZE, "RIP");

  /* Add the constraint in the PathConstraints list */
  ap.addPathConstraint(se->getID());

}


void JnleIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void JnleIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void JnleIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *JnleIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "JNLE");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

