/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <LeaIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


LeaIRBuilder::LeaIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void LeaIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void LeaIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void LeaIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *dis2e, *base2e, *index2e, *scale2e;
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();
  auto displacement = this->operands[1].getDisplacement().getValue();
  auto baseReg = this->operands[1].getBaseReg();
  auto indexReg = this->operands[1].getIndexReg();
  auto memoryScale = this->operands[1].getMemoryScale().getValue();

  /* Base register */
  if (baseReg.getTritonRegId()) {
    /* If the base register is RIP, we must use nextAddress */
    if (baseReg.getTritonRegId() == ID_RIP)
      base2e = smt2lib::bv(this->nextAddress, regSize * REG_SIZE);
    else
      base2e = ap.buildSymbolicRegOperand(baseReg, regSize);
  }
  else
    base2e = smt2lib::bv(0, regSize * REG_SIZE);

  /* Index register if it exists */
  if (indexReg.getTritonRegId())
    index2e = ap.buildSymbolicRegOperand(indexReg, regSize);
  else
    index2e = smt2lib::bv(0, regSize * REG_SIZE);

  /* Displacement */
  dis2e = smt2lib::bv(displacement, regSize * REG_SIZE);

  /* Scale */
  scale2e = smt2lib::bv(memoryScale, regSize * REG_SIZE);

  /* final SMT expression */
  /* Effective address = Displacement + BaseReg + IndexReg * Scale */
  expr = smt2lib::bvadd(dis2e, smt2lib::bvadd(base2e, smt2lib::bvmul(index2e, scale2e)));

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint via the concretization */
  if (ap.isRegTainted(baseReg) == TAINTED)
    ap.assignmentSpreadTaintRegReg(se, reg, baseReg);
  else
    ap.assignmentSpreadTaintRegReg(se, reg, indexReg);

}


void LeaIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void LeaIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *LeaIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "LEA");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

#endif /* LIGHT_VERSION */

