#include <iostream>
#include <sstream>
#include <stdexcept>

#include "CqoIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


CqoIRBuilder::CqoIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void CqoIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se1, *se2, *se3;
  std::stringstream expr1, expr2, expr3, op1;

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(ID_RAX, REG_SIZE, 63, 0);

  /* Expression 1: TMP = 128 bitvec (RDX:RAX) */
  expr1 << smt2lib::sx(op1.str(), 64);
  se1 = ap.createSE(expr1, "Temporary variable");

  /* Expression 2: RAX = TMP[63...0] */
  expr2 << smt2lib::extract(63, 0, se1->getID2Str());
  se2 = ap.createRegSE(expr2, ID_RAX, "RAX");

  /* Expression 3: RDX = TMP[127...64] */
  expr3 << smt2lib::extract(127, 64, se1->getID2Str());
  se3 = ap.createRegSE(expr3, ID_RDX, "RDX");

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se3, ID_RDX, ID_RAX);

  /* Add the symbolic element to the current inst */
  inst.addElement(se1);
  inst.addElement(se2);
  inst.addElement(se3);
}


Inst *CqoIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "CQO");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

