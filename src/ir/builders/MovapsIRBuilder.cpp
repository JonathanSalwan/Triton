#include <algorithm>
#include <sstream>
#include <stdexcept>

#include "MovapsIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


MovapsIRBuilder::MovapsIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void MovapsIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovapsIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint64_t          reg1      = this->operands[0].getValue();
  uint64_t          reg2      = this->operands[1].getValue();
  uint64_t          reg2Size  = this->operands[1].getSize();
  uint64_t          symReg2   = ap.getRegSymbolicID(reg2);

  /* Create the SMT semantic */
  if (symReg2 != UNSET)
    expr << smt2lib::extract(reg2Size, "#" + std::to_string(symReg2));
  else
    expr << smt2lib::bv(ap.getSSERegisterValue(reg2), REG_SIZE_SSE_BIT);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg1);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegReg(se, reg1, reg2);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovapsIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint32_t          readSize = this->operands[1].getSize();
  uint64_t          mem      = this->operands[1].getValue();
  uint64_t          reg      = this->operands[0].getValue();
  uint64_t          symMem   = ap.getMemSymbolicID(mem);

  /* Create the SMT semantic */
  if (symMem != UNSET)
    expr << smt2lib::extract(readSize, "#" + std::to_string(symMem));
  else
    expr << smt2lib::bv(ap.getMemValue(mem, readSize), REG_SIZE_SSE_BIT);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se, reg, mem, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovapsIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovapsIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint32_t          writeSize = this->operands[0].getSize();
  uint64_t          mem       = this->operands[0].getValue();
  uint64_t          reg       = this->operands[1].getValue();
  uint64_t          regSize   = this->operands[1].getSize();
  uint64_t          symReg    = ap.getRegSymbolicID(reg);

  /* Create the SMT semantic */
  if (symReg != UNSET)
    expr << smt2lib::extract(regSize, "#" + std::to_string(symReg));
  else
    expr << smt2lib::bv(ap.getSSERegisterValue(reg), REG_SIZE_SSE_BIT);

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemReg(se, mem, reg, writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


Inst *MovapsIRBuilder::process(AnalysisProcessor &ap) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "MOVAPS");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

