#include <iostream>
#include <sstream>
#include <stdexcept>

#include "LeaveIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


LeaveIRBuilder::LeaveIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


static SymbolicElement *alignStack(AnalysisProcessor &ap, uint32_t readSize)
{
  SymbolicElement     *se;
  std::stringstream   expr, op1, op2;
  uint64_t            symReg = ap.getRegSymbolicID(ID_RSP);

  /*
   * Create the SMT semantic.
   */
  if (symReg != UNSET)
    op1 << "#" << std::dec << symReg;
  else
    op1 << smt2lib::bv(ap.getRegisterValue(REG_RSP), readSize * REG_SIZE);

  op2 << smt2lib::bv(readSize, readSize * REG_SIZE);

  expr << smt2lib::bvadd(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_RSP);

  /* Apply the taint */
  se->isTainted = ap.isRegTainted(ID_RSP);

  return se;
}

void LeaveIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement     *se1, *se2;
  std::stringstream   expr1, expr2;
  uint64_t            symRegRBP = ap.getRegSymbolicID(ID_RBP);
  uint64_t            readMem   = std::get<1>(this->operands[0]); // The src memory read
  uint32_t            readSize  = std::get<2>(this->operands[0]);
  uint64_t            symMem    = ap.getMemSymbolicID(readMem);

  // RSP = RBP; -----------------------------
  if (symRegRBP != UNSET)
    expr1 << smt2lib::extract(8, "#" + std::to_string(symRegRBP));
  else
    expr1 << smt2lib::bv(ap.getRegisterValue(REG_RBP), 8 * REG_SIZE);

  /* Create the symbolic element */
  se1 = ap.createRegSE(expr1, ID_RSP);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegReg(se1, ID_RSP, ID_RBP);
  // RSP = RBP; -----------------------------

  // RBP = Pop(); ---------------------------
  if (symMem != UNSET)
    expr2 << "#" << std::dec << symMem;
  else
    expr2 << smt2lib::bv(ap.getMemValue(readMem, readSize), readSize * REG_SIZE);

  /* Create the symbolic element */
  se2 = ap.createRegSE(expr2, ID_RBP);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se2, ID_RBP, readMem, readSize);
  // RBP = Pop(); ---------------------------
  
  /* Add the symbolic element to the current inst */
  inst.addElement(se1);
  inst.addElement(se2);
  inst.addElement(alignStack(ap, readSize));
}


Inst *LeaveIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "LEAVE");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

