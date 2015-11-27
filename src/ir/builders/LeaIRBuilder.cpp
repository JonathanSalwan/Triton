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


LeaIRBuilder::LeaIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void LeaIRBuilder::regImm(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void LeaIRBuilder::regReg(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void LeaIRBuilder::regMem(Inst &inst) const {
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
    if (baseReg.getTritonRegId() == ID_IP)
      base2e = smt2lib::bv(this->nextAddress, regSize * BYTE_SIZE_BIT);
    else
      base2e = ap.buildSymbolicRegOperand(baseReg, regSize);
  }
  else
    base2e = smt2lib::bv(0, regSize * BYTE_SIZE_BIT);

  /* Index register if it exists */
  if (indexReg.getTritonRegId())
    index2e = ap.buildSymbolicRegOperand(indexReg, regSize);
  else
    index2e = smt2lib::bv(0, regSize * BYTE_SIZE_BIT);

  /* Displacement */
  dis2e = smt2lib::bv(displacement, regSize * BYTE_SIZE_BIT);

  /* Scale */
  scale2e = smt2lib::bv(memoryScale, regSize * BYTE_SIZE_BIT);

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


void LeaIRBuilder::memImm(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void LeaIRBuilder::memReg(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *LeaIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "LEA");
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

