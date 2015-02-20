#include <iostream>
#include <sstream>
#include <stdexcept>

#include "AddIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


AddIRBuilder::AddIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void AddIRBuilder::regImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64_t          reg     = std::get<1>(this->operands[0]);
  uint64_t          imm     = std::get<1>(this->operands[1]);

  uint64_t          symReg  = ap.getRegSymbolicID(ctxH.translateRegID(reg));
  uint32_t          regSize = ctxH.getRegisterSize(reg);

  /* Create the SMT semantic */
  /* OP_1 */
  if (symReg != UNSET)
    op1 << "#" << std::dec << symReg;
  else
    op1 << smt2lib::bv(ctxH.getRegisterValue(reg), regSize * REG_SIZE);

  /* Finale expr */
  expr << smt2lib::bvadd(op1.str(), smt2lib::bv(imm, regSize * REG_SIZE));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ctxH.translateRegID(reg));

  /* Apply the taint */
  ap.aluSpreadTaintRegImm(se, ctxH.translateRegID(reg));

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::cf(se, ap, op1));
  inst.addElement(EflagsBuilder::zf(se, ap, regSize));
  inst.addElement(EflagsBuilder::sf(se, ap, regSize));
}


void AddIRBuilder::regReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint64_t          reg1    = std::get<1>(this->operands[0]);
  uint64_t          reg2    = std::get<1>(this->operands[1]);

  uint64_t          symReg1 = ap.getRegSymbolicID(ctxH.translateRegID(reg1));
  uint64_t          symReg2 = ap.getRegSymbolicID(ctxH.translateRegID(reg2));
  uint32_t          regSize = ctxH.getRegisterSize(reg1);


  /* Create the SMT semantic */
  // OP_1
  if (symReg1 != UNSET)
    op1 << "#" << std::dec << symReg1;
  else
    op1 << smt2lib::bv(ctxH.getRegisterValue(reg1), regSize * REG_SIZE);

  // OP_2
  if (symReg2 != UNSET)
    op2 << "#" << std::dec << symReg2;
  else
    op2 << smt2lib::bv(ctxH.getRegisterValue(reg2), regSize * REG_SIZE);

  // Final expr
  expr << smt2lib::bvadd(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ctxH.translateRegID(reg1));

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, ctxH.translateRegID(reg1), ctxH.translateRegID(reg2));

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::cf(se, ap, op1));
  inst.addElement(EflagsBuilder::zf(se, ap, regSize));
  inst.addElement(EflagsBuilder::sf(se, ap, regSize));
}


void AddIRBuilder::regMem(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint32_t          readSize = std::get<2>(this->operands[1]);
  uint64_t          mem      = std::get<1>(this->operands[1]);
  uint64_t          reg      = std::get<1>(this->operands[0]);

  uint64_t          symReg   = ap.getRegSymbolicID(ctxH.translateRegID(reg));
  uint64_t          symMem   = ap.getMemorySymbolicID(mem);
  uint32_t          regSize  = ctxH.getRegisterSize(reg);

  /* Create the SMT semantic */
  // OP_1
  if (symReg != UNSET)
    op1 << "#" << std::dec << symReg;
  else
    op1 << smt2lib::bv(ctxH.getRegisterValue(reg), readSize * REG_SIZE);

  // OP_2
  if (symMem != UNSET)
    op2 << "#" << std::dec << symMem;
  else
    op2 << smt2lib::bv(ctxH.getMemoryValue(mem, readSize), readSize * REG_SIZE);

  // Final expr
  expr << smt2lib::bvadd(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ctxH.translateRegID(reg));

  /* Apply the taint */
  ap.aluSpreadTaintRegMem(se, ctxH.translateRegID(reg), mem, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::cf(se, ap, op1));
  inst.addElement(EflagsBuilder::zf(se, ap, regSize));
  inst.addElement(EflagsBuilder::sf(se, ap, regSize));
}


void AddIRBuilder::memImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint32_t          writeSize = std::get<2>(this->operands[0]);
  uint64_t          mem       = std::get<1>(this->operands[0]);
  uint64_t          imm       = std::get<1>(this->operands[1]);

  uint64_t          symMem    = ap.getMemorySymbolicID(mem);

  /* Create the SMT semantic */
  /* OP_1 */
  if (symMem != UNSET)
    op1 << "#" << std::dec << symMem;
  else
    op1 << smt2lib::bv(ctxH.getMemoryValue(mem, writeSize), writeSize * REG_SIZE);

  /* Final expr */
  expr << smt2lib::bvadd(op1.str(), smt2lib::bv(imm, writeSize * REG_SIZE));

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.aluSpreadTaintMemImm(se, mem, writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::cf(se, ap, op1));
  inst.addElement(EflagsBuilder::zf(se, ap, writeSize));
  inst.addElement(EflagsBuilder::sf(se, ap, writeSize));
}


void AddIRBuilder::memReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint32_t          writeSize = std::get<2>(this->operands[0]);
  uint64_t          mem       = std::get<1>(this->operands[0]);
  uint64_t          reg       = std::get<1>(this->operands[1]);

  uint64_t          symReg    = ap.getRegSymbolicID(ctxH.translateRegID(reg));
  uint64_t          symMem    = ap.getMemorySymbolicID(mem);

  /* Create the SMT semantic */
  // OP_1
  if (symMem != UNSET)
    op1 << "#" << std::dec << symMem;
  else
    op1 << smt2lib::bv(ctxH.getMemoryValue(mem, writeSize), writeSize * REG_SIZE);

  // OP_1
  if (symReg != UNSET)
    op2 << "#" << std::dec << symReg;
  else
    op2 << smt2lib::bv(ctxH.getRegisterValue(reg), writeSize * REG_SIZE);

  // Final expr
  expr << smt2lib::bvadd(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.aluSpreadTaintMemReg(se, mem, ctxH.translateRegID(reg), writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::cf(se, ap, op1));
  inst.addElement(EflagsBuilder::zf(se, ap, writeSize));
  inst.addElement(EflagsBuilder::sf(se, ap, writeSize));
}


Inst *AddIRBuilder::process(const ContextHandler &ctxH, AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(this->address, this->disas);

  try {
    this->templateMethod(ctxH, ap, *inst, this->operands, "ADD");
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

