/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <JnbeIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


JnbeIRBuilder::JnbeIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void JnbeIRBuilder::imm(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *cf, *zf;
  auto imm = this->operands[0].getImm().getValue();

  /* Create the SMT semantic */
  cf = ap.buildSymbolicFlagOperand(ID_TMP_CF);
  zf = ap.buildSymbolicFlagOperand(ID_TMP_ZF);

  /* 
   * Finale expr
   * JNBE: Jump if not below or equal (CF =0 and ZF =0).
   * SMT: ( = (bvand (bvnot zf) (bvnot cf)) (_ bv1 1))
   */
  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvand(
                smt2lib::bvnot(cf),
                smt2lib::bvnot(zf)
              ),
              smt2lib::bvtrue()
            ),
            smt2lib::bv(imm, REG_SIZE_BIT),
            smt2lib::bv(this->nextAddress, REG_SIZE_BIT));

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, ID_TMP_RIP, REG_SIZE, "Program Counter");

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, ID_TMP_RIP, ID_TMP_CF);
  ap.aluSpreadTaintRegReg(se, ID_TMP_RIP, ID_TMP_ZF);

  /* Add the constraint in the PathConstraints list */
  ap.addPathConstraint(se->getID());
}


void JnbeIRBuilder::reg(Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void JnbeIRBuilder::mem(Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void JnbeIRBuilder::none(Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *JnbeIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "JNBE");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

#endif /* LIGHT_VERSION */

