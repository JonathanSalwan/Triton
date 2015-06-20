#include <iostream>
#include <sstream>
#include <stdexcept>

#include <CwdeIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicElement.h>


CwdeIRBuilder::CwdeIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void CwdeIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(ID_RAX, REG_SIZE, 16, 0);

  /* Finale expr */
  expr << smt2lib::sx(op1.str(), 16);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_RAX, DWORD_SIZE);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, ID_RAX, ID_RAX);
}


Inst *CwdeIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "CWDE");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

