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


void LeaveIRBuilder::none(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement     *se1, *se2;
  std::stringstream   expr1, expr2;
  uint64_t            symRegRBP = ap.getRegSymbolicID(ID_RBP);
  uint64_t            readMem   = std::get<1>(this->operands[0]); // The src memory read
  uint32_t            readSize  = std::get<2>(this->operands[0]);
  uint64_t            symMem    = ap.getMemorySymbolicID(readMem);

  // RSP = RBP; -----------------------------
  if (symRegRBP != UNSET)
    expr1 << smt2lib::extract(8, "#" + std::to_string(symRegRBP));
  else
    expr1 << smt2lib::bv(ctxH.getRegisterValue(REG_RBP), 8 * REG_SIZE);

  /* Create the symbolic element */
  se1 = ap.createRegSE(expr1, ID_RSP);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegReg(se1, ID_RSP, ID_RBP);
  // RSP = RBP; -----------------------------

  // RBP = Pop(); ---------------------------
  if (symMem != UNSET)
    expr2 << "#" << std::dec << symMem;
  else
    expr2 << smt2lib::bv(ctxH.getMemoryValue(readMem, readSize), readSize * REG_SIZE);

  /* Create the symbolic element */
  se2 = ap.createRegSE(expr2, ID_RBP);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se2, ID_RBP, readMem, readSize);
  // RBP = Pop(); ---------------------------
  
  /* Add the symbolic element to the current inst */
  inst.addElement(se1);
  inst.addElement(se2);
}


Inst *LeaveIRBuilder::process(const ContextHandler &ctxH, AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ctxH.getThreadId(), this->address, this->disas);

  try {
    this->templateMethod(ctxH, ap, *inst, this->operands, "LEAVE");
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

