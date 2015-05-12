#include <algorithm>
#include <sstream>
#include <stdexcept>

#include "MovapdIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


MovapdIRBuilder::MovapdIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void MovapdIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovapdIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint64_t          reg1      = std::get<1>(this->operands[0]);
  uint64_t          reg2      = std::get<1>(this->operands[1]);
  uint64_t          reg2Size  = std::get<2>(this->operands[1]);
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


void MovapdIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint32_t          readSize = std::get<2>(this->operands[1]);
  uint64_t          mem      = std::get<1>(this->operands[1]);
  uint64_t          reg      = std::get<1>(this->operands[0]);
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


void MovapdIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovapdIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint32_t          writeSize = std::get<2>(this->operands[0]);
  uint64_t          mem       = std::get<1>(this->operands[0]);
  uint64_t          reg       = std::get<1>(this->operands[1]);
  uint64_t          regSize   = std::get<2>(this->operands[1]);
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


Inst *MovapdIRBuilder::process(AnalysisProcessor &ap) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "MOVAPD");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

