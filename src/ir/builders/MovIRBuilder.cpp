#include <algorithm>
#include <sstream>
#include <stdexcept>

#include "MovIRBuilder.h"
#include "Registers.h"
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
  return (std::max(size1, size2) * REG_SIZE) - (std::min(size1, size2) * REG_SIZE);
}


void MovIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint64_t          reg = std::get<1>(this->operands[0]);
  uint64_t          imm = std::get<1>(this->operands[1]);
  uint64_t          size = std::get<2>(this->operands[0]);

  /* Create the SMT semantic */
  expr << smt2lib::bv(imm, size * REG_SIZE);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegImm(se, reg);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint64_t          reg1    = std::get<1>(this->operands[0]);
  uint64_t          reg2    = std::get<1>(this->operands[1]);
  uint64_t          size1 = std::get<2>(this->operands[0]);
  uint64_t          size2 = std::get<2>(this->operands[1]);

  uint64_t          symReg2 = ap.getRegSymbolicID(reg2);

  /* Create the SMT semantic */
  if (symReg2 != UNSET)
    expr << smt2lib::extract(size2, "#" + std::to_string(symReg2));
  else
    expr << smt2lib::bv(ap.getRegisterValue(reg2), size1 * REG_SIZE);

  expr.str(this->extender(expr.str(), deltaSize(size1, size2)));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg1);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegReg(se, reg1, reg2);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint32_t          readSize = std::get<2>(this->operands[1]);
  uint64_t          mem      = std::get<1>(this->operands[1]);
  uint64_t          reg      = std::get<1>(this->operands[0]);
  uint64_t          regSize  = std::get<2>(this->operands[0]);

  uint64_t          symMem   = ap.getMemSymbolicID(mem);

  /* Create the SMT semantic */
  if (symMem != UNSET)
    expr << smt2lib::extract(readSize, "#" + std::to_string(symMem));
  else
    expr << smt2lib::bv(ap.getMemValue(mem, readSize), readSize * REG_SIZE);

  expr.str(this->extender(expr.str(), deltaSize(regSize, readSize)));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se, reg, mem, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint32_t          writeSize = std::get<2>(this->operands[0]);
  uint64_t          mem       = std::get<1>(this->operands[0]);
  uint64_t          imm       = std::get<1>(this->operands[1]);

  /* Create the SMT semantic */
  expr << smt2lib::bv(imm, writeSize * REG_SIZE);

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemImm(se, mem, writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
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
    expr << smt2lib::bv(ap.getRegisterValue(reg), writeSize * REG_SIZE);

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemReg(se, mem, reg, writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


Inst *MovIRBuilder::process(AnalysisProcessor &ap) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "MOV");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

