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


void AddIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint64_t          reg     = std::get<1>(this->operands[0]);
  uint64_t          imm     = std::get<1>(this->operands[1]);

  uint64_t          symReg  = ap.getRegSymbolicID(ap.convertPinReg2TritonReg(reg));
  uint32_t          regSize = ap.getRegisterSize(reg);

  /* Create the SMT semantic */
  /* OP_1 */
  if (symReg != UNSET)
    op1 << smt2lib::extract(regSize, "#" + std::to_string(symReg));
  else
    op1 << smt2lib::bv(ap.getRegisterValue(reg), regSize * REG_SIZE);

  /* OP_2 */
  op2 << smt2lib::bv(imm, regSize * REG_SIZE);

  /* Finale expr */
  expr << smt2lib::bvadd(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ap.convertPinReg2TritonReg(reg));

  /* Apply the taint */
  ap.aluSpreadTaintRegImm(se, ap.convertPinReg2TritonReg(reg));

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::af(se, ap, regSize, op1, op2));
  inst.addElement(EflagsBuilder::cf(se, ap, op1));
  inst.addElement(EflagsBuilder::of(se, ap, regSize, op1, op2));
  inst.addElement(EflagsBuilder::pf(se, ap));
  inst.addElement(EflagsBuilder::sf(se, ap, regSize));
  inst.addElement(EflagsBuilder::zf(se, ap, regSize));
}


void AddIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint64_t          reg1     = std::get<1>(this->operands[0]);
  uint64_t          reg2     = std::get<1>(this->operands[1]);

  uint64_t          symReg1  = ap.getRegSymbolicID(ap.convertPinReg2TritonReg(reg1));
  uint64_t          symReg2  = ap.getRegSymbolicID(ap.convertPinReg2TritonReg(reg2));
  uint32_t          regSize1 = ap.getRegisterSize(reg1);
  uint32_t          regSize2 = ap.getRegisterSize(reg2);


  /* Create the SMT semantic */
  // OP_1
  if (symReg1 != UNSET)
    op1 << smt2lib::extract(regSize1, "#" + std::to_string(symReg1));
  else
    op1 << smt2lib::bv(ap.getRegisterValue(reg1), regSize1 * REG_SIZE);

  // OP_2
  if (symReg2 != UNSET)
    op2 << smt2lib::extract(regSize2, "#" + std::to_string(symReg2));
  else
    op2 << smt2lib::bv(ap.getRegisterValue(reg2), regSize2 * REG_SIZE);

  // Final expr
  expr << smt2lib::bvadd(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ap.convertPinReg2TritonReg(reg1));

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, ap.convertPinReg2TritonReg(reg1), ap.convertPinReg2TritonReg(reg2));

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::af(se, ap, regSize1, op1, op2));
  inst.addElement(EflagsBuilder::cf(se, ap, op1));
  inst.addElement(EflagsBuilder::of(se, ap, regSize1, op1, op2));
  inst.addElement(EflagsBuilder::pf(se, ap));
  inst.addElement(EflagsBuilder::sf(se, ap, regSize1));
  inst.addElement(EflagsBuilder::zf(se, ap, regSize1));
}


void AddIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint32_t          readSize = std::get<2>(this->operands[1]);
  uint64_t          mem      = std::get<1>(this->operands[1]);
  uint64_t          reg      = std::get<1>(this->operands[0]);

  uint64_t          symReg   = ap.getRegSymbolicID(ap.convertPinReg2TritonReg(reg));
  uint64_t          symMem   = ap.getMemSymbolicID(mem);
  uint32_t          regSize  = ap.getRegisterSize(reg);

  /* Create the SMT semantic */
  // OP_1
  if (symReg != UNSET)
    op1 << smt2lib::extract(regSize, "#" + std::to_string(symReg));
  else
    op1 << smt2lib::bv(ap.getRegisterValue(reg), readSize * REG_SIZE);

  // OP_2
  if (symMem != UNSET)
    op2 << "#" << std::dec << symMem;
  else
    op2 << smt2lib::bv(ap.getMemValue(mem, readSize), readSize * REG_SIZE);

  // Final expr
  expr << smt2lib::bvadd(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ap.convertPinReg2TritonReg(reg));

  /* Apply the taint */
  ap.aluSpreadTaintRegMem(se, ap.convertPinReg2TritonReg(reg), mem, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::af(se, ap, regSize, op1, op2));
  inst.addElement(EflagsBuilder::cf(se, ap, op1));
  inst.addElement(EflagsBuilder::of(se, ap, regSize, op1, op2));
  inst.addElement(EflagsBuilder::pf(se, ap));
  inst.addElement(EflagsBuilder::sf(se, ap, regSize));
  inst.addElement(EflagsBuilder::zf(se, ap, regSize));
}


void AddIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint32_t          writeSize = std::get<2>(this->operands[0]);
  uint64_t          mem       = std::get<1>(this->operands[0]);
  uint64_t          imm       = std::get<1>(this->operands[1]);

  uint64_t          symMem    = ap.getMemSymbolicID(mem);

  /* Create the SMT semantic */
  /* OP_1 */
  if (symMem != UNSET)
    op1 << "#" << std::dec << symMem;
  else
    op1 << smt2lib::bv(ap.getMemValue(mem, writeSize), writeSize * REG_SIZE);

  /* OP_2 */
  op2 << smt2lib::bv(imm, writeSize * REG_SIZE);

  /* Final expr */
  expr << smt2lib::bvadd(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.aluSpreadTaintMemImm(se, mem, writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::af(se, ap, writeSize, op1, op2));
  inst.addElement(EflagsBuilder::cf(se, ap, op1));
  inst.addElement(EflagsBuilder::of(se, ap, writeSize, op1, op2));
  inst.addElement(EflagsBuilder::pf(se, ap));
  inst.addElement(EflagsBuilder::sf(se, ap, writeSize));
  inst.addElement(EflagsBuilder::zf(se, ap, writeSize));
}


void AddIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint32_t          writeSize = std::get<2>(this->operands[0]);
  uint64_t          mem       = std::get<1>(this->operands[0]);
  uint64_t          reg       = std::get<1>(this->operands[1]);
  uint32_t          regSize   = ap.getRegisterSize(reg);

  uint64_t          symReg    = ap.getRegSymbolicID(ap.convertPinReg2TritonReg(reg));
  uint64_t          symMem    = ap.getMemSymbolicID(mem);

  /* Create the SMT semantic */
  // OP_1
  if (symMem != UNSET)
    op1 << "#" << std::dec << symMem;
  else
    op1 << smt2lib::bv(ap.getMemValue(mem, writeSize), writeSize * REG_SIZE);

  // OP_1
  if (symReg != UNSET)
    op2 << smt2lib::extract(regSize, "#" + std::to_string(symReg));
  else
    op2 << smt2lib::bv(ap.getRegisterValue(reg), writeSize * REG_SIZE);

  // Final expr
  expr << smt2lib::bvadd(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.aluSpreadTaintMemReg(se, mem, ap.convertPinReg2TritonReg(reg), writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::af(se, ap, writeSize, op1, op2));
  inst.addElement(EflagsBuilder::cf(se, ap, op1));
  inst.addElement(EflagsBuilder::of(se, ap, writeSize, op1, op2));
  inst.addElement(EflagsBuilder::pf(se, ap));
  inst.addElement(EflagsBuilder::sf(se, ap, writeSize));
  inst.addElement(EflagsBuilder::zf(se, ap, writeSize));
}


Inst *AddIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "ADD");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

