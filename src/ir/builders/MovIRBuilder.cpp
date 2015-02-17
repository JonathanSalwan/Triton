#include <algorithm>
#include <sstream>
#include <stdexcept>

#include "MovIRBuilder.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


// Returns this argument. Only useful for fill the extender member.
template<typename T, typename INT>
static T nullf(T t, INT size) {
  return t;
}

MovIRBuilder::MovIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly),
  extender(&nullf<std::string, uint64_t>) {

}


// Return the difference in bits of two registers size given in bytes.
static uint64_t deltaSize(uint64_t size1, uint64_t size2) {
  return std::max(size1, size2)*8 - std::min(size1, size2)*8;
}

void MovIRBuilder::regImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint64_t          reg = std::get<1>(this->operands[0]);
  uint64_t          imm = std::get<1>(this->operands[1]);
  uint64_t          size = ctxH.getRegisterSize(reg);

  /* Create the SMT semantic */
  expr << smt2lib::bv(imm, size);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ctxH.translateRegID(reg));

  /* Apply the taint */
  ap.assignmentSpreadTaintRegImm(se, ctxH.translateRegID(reg));

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovIRBuilder::regReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint64_t          reg1    = std::get<1>(this->operands[0]);
  uint64_t          reg2    = std::get<1>(this->operands[1]);
  uint64_t          size1 = ctxH.getRegisterSize(reg1);
  uint64_t          size2 = ctxH.getRegisterSize(reg2);

  uint64_t          symReg2 = ap.getRegSymbolicID(ctxH.translateRegID(reg2));

  /* Create the SMT semantic */
  if (symReg2 != UNSET)
    expr << "#" << std::dec << symReg2;
  else
    expr << smt2lib::bv(ctxH.getRegisterValue(reg2), size1);

  expr.str(this->extender(expr.str(), deltaSize(size1, size2)));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ctxH.translateRegID(reg1));

  /* Apply the taint */
  ap.assignmentSpreadTaintRegReg(se, ctxH.translateRegID(reg1), ctxH.translateRegID(reg2));

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovIRBuilder::regMem(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint32_t          readSize = std::get<2>(this->operands[1]);
  uint64_t          mem      = std::get<1>(this->operands[1]);
  uint64_t          reg      = std::get<1>(this->operands[0]);
  uint64_t          regSize  = ctxH.getRegisterSize(reg);

  uint64_t          symMem   = ap.getMemorySymbolicID(mem);

  /* Create the SMT semantic */
  if (symMem != UNSET)
    expr << "#" << std::dec << symMem;
  else
    expr << smt2lib::bv(ctxH.getMemoryValue(mem, readSize), readSize);

  expr.str(this->extender(expr.str(), deltaSize(regSize, readSize)));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ctxH.translateRegID(reg));

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se, ctxH.translateRegID(reg), mem, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovIRBuilder::memImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint32_t          writeSize = std::get<2>(this->operands[0]);
  uint64_t          mem       = std::get<1>(this->operands[0]);
  uint64_t          imm       = std::get<1>(this->operands[1]);

  /* Create the SMT semantic */
  expr << smt2lib::bv(imm, writeSize);

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemImm(se, mem, writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovIRBuilder::memReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint32_t          writeSize = std::get<2>(this->operands[0]);
  uint64_t          mem       = std::get<1>(this->operands[0]);
  uint64_t          reg       = std::get<1>(this->operands[1]);

  uint64_t          symReg    = ap.getRegSymbolicID(ctxH.translateRegID(reg));

  /* Create the SMT semantic */
  if (symReg != UNSET)
    expr << "#" << std::dec << symReg;
  else
    expr << smt2lib::bv(ctxH.getRegisterValue(reg), writeSize);

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemReg(se, mem, ctxH.translateRegID(reg), writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


Inst *MovIRBuilder::process(const ContextHandler &ctxH, AnalysisProcessor &ap) const {
  checkSetup();

  Inst *inst = new Inst(this->address, this->disas);

  try {
    this->templateMethod(ctxH, ap, *inst, this->operands, "MOV");
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

