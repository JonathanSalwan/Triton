#include <iostream>
#include <sstream>
#include <stdexcept>

#include <LeaveIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicElement.h>


LeaveIRBuilder::LeaveIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


static SymbolicElement *alignStack(Inst &inst, AnalysisProcessor &ap, uint32 readSize)
{
  SymbolicElement     *se;
  std::stringstream   expr, op1, op2;

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(ID_RSP, REG_SIZE);
  op2 << smt2lib::bv(readSize, readSize * REG_SIZE);

  expr << smt2lib::bvadd(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_RSP, REG_SIZE, "Aligns stack");

  /* Apply the taint */
  se->isTainted = ap.isRegTainted(ID_RSP);

  return se;
}

void LeaveIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement     *se1, *se2;
  std::stringstream   expr1, expr2;
  uint64              readMem   = this->operands[0].getValue(); // The src memory read
  uint32              readSize  = this->operands[0].getSize();

  // RSP = RBP; -----------------------------
  expr1 << ap.buildSymbolicRegOperand(ID_RBP, REG_SIZE);

  /* Create the symbolic element */
  se1 = ap.createRegSE(inst, expr1, ID_RSP, REG_SIZE);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegReg(se1, ID_RSP, ID_RBP);
  // RSP = RBP; -----------------------------

  // RBP = Pop(); ---------------------------
  expr2 << ap.buildSymbolicMemOperand(readMem, readSize);

  /* Create the symbolic element */
  se2 = ap.createRegSE(inst, expr2, ID_RBP, REG_SIZE);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se2, ID_RBP, readMem, readSize);
  // RBP = Pop(); ---------------------------
  
  /* Add the symbolic element to the current inst */
  alignStack(inst, ap, readSize);
}


Inst *LeaveIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "LEAVE");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

