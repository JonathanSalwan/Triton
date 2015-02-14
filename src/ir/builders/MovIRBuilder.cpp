#include <iostream>
#include <sstream>
#include <stdexcept>

#include "MovIRBuilder.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"



MovIRBuilder::MovIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {

}


void MovIRBuilder::regImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint64_t          reg = std::get<1>(_operands[0]);
  uint64_t          imm = std::get<1>(_operands[1]);

  /* Create the SMT semantic */
  expr << smt2lib::bv(imm, ctxH.getRegisterSize(reg));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ctxH.translateRegID(reg));

  /* Apply the taint */
  ap.spreadTaintRegImm(se, ctxH.translateRegID(reg));

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovIRBuilder::regReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint64_t          reg1    = std::get<1>(_operands[0]);
  uint64_t          reg2    = std::get<1>(_operands[1]);

  uint64_t          symReg2 = ap.getRegSymbolicID(ctxH.translateRegID(reg2));

  /* Create the SMT semantic */
  if (symReg2 != UNSET)
    expr << "#" << std::dec << symReg2;
  else
    expr << smt2lib::bv(ctxH.getRegisterValue(reg2), ctxH.getRegisterSize(reg1));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ctxH.translateRegID(reg1));

  /* Apply the taint */
  ap.spreadTaintRegReg(se, ctxH.translateRegID(reg1), ctxH.translateRegID(reg2));

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovIRBuilder::regMem(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint32_t          readSize = std::get<2>(_operands[1]);
  uint64_t          mem      = std::get<1>(_operands[1]);
  uint64_t          reg      = std::get<1>(_operands[0]);

  uint64_t          symMem   = ap.getMemorySymbolicID(mem);

  /* Create the SMT semantic */
  if (symMem != UNSET)
    expr << "#" << std::dec << symMem;
  else
    expr << smt2lib::bv(ctxH.getMemoryValue(mem, readSize), readSize);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ctxH.translateRegID(reg));

  /* Apply the taint */
  ap.spreadTaintRegMem(se, ctxH.translateRegID(reg), mem);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovIRBuilder::memImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint32_t          writeSize = std::get<2>(_operands[0]);
  uint64_t          mem       = std::get<1>(_operands[0]);
  uint64_t          imm       = std::get<1>(_operands[1]);

  /* Create the SMT semantic */
  expr << smt2lib::bv(imm, writeSize);

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.spreadTaintMemImm(se, mem);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovIRBuilder::memReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint32_t          writeSize = std::get<2>(_operands[0]);
  uint64_t          mem       = std::get<1>(_operands[0]);
  uint64_t          reg       = std::get<1>(_operands[1]);

  uint64_t          symReg    = ap.getRegSymbolicID(ctxH.translateRegID(reg));

  /* Create the SMT semantic */
  if (symReg != UNSET)
    expr << "#" << std::dec << symReg;
  else
    expr << smt2lib::bv(ctxH.getRegisterValue(reg), writeSize);

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.spreadTaintMemReg(se, mem, ctxH.translateRegID(reg));

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


Inst *MovIRBuilder::process(const ContextHandler &ctxH, AnalysisProcessor &ap) const {
  checkSetup();

  Inst *inst = new Inst(_address, _disas);

  try {
    this->templateMethod(ctxH, ap, *inst, _operands, "MOV");
  }
  catch (std::exception &e) {
    delete inst;
    throw e;
  }

  return inst;
}

