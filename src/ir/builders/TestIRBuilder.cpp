#include <iostream>
#include <sstream>
#include <stdexcept>

#include "TestIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


TestIRBuilder::TestIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void TestIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint64_t          reg     = std::get<1>(this->operands[0]);
  uint64_t          imm     = std::get<1>(this->operands[1]);

  uint64_t          symReg  = ap.getRegSymbolicID(reg);
  uint32_t          regSize = std::get<2>(this->operands[0]);

  /* Create the SMT semantic */
  /* OP_1 */
  if (symReg != UNSET)
    op1 << smt2lib::extract(regSize, "#" + std::to_string(symReg));
  else
    op1 << smt2lib::bv(ap.getRegisterValue(reg), regSize * REG_SIZE);

  /* OP_2 */
  op2 << smt2lib::bv(imm, regSize * REG_SIZE);

  /* Finale expr */
  expr << smt2lib::bvand(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createSE(expr);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::clearFlag(ap, ID_CF, "Clears carry flag"));
  inst.addElement(EflagsBuilder::clearFlag(ap, ID_OF, "Clears overflow flag"));
  inst.addElement(EflagsBuilder::pf(se, ap));
  inst.addElement(EflagsBuilder::sf(se, ap, regSize));
  inst.addElement(EflagsBuilder::zf(se, ap, regSize));
}


void TestIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint64_t          reg1     = std::get<1>(this->operands[0]);
  uint64_t          reg2     = std::get<1>(this->operands[1]);

  uint64_t          symReg1  = ap.getRegSymbolicID(reg1);
  uint64_t          symReg2  = ap.getRegSymbolicID(reg2);
  uint32_t          regSize1 = std::get<2>(this->operands[0]);
  uint32_t          regSize2 = std::get<2>(this->operands[1]);


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
  expr << smt2lib::bvand(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createSE(expr);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::clearFlag(ap, ID_CF, "Clears carry flag"));
  inst.addElement(EflagsBuilder::clearFlag(ap, ID_OF, "Clears overflow flag"));
  inst.addElement(EflagsBuilder::pf(se, ap));
  inst.addElement(EflagsBuilder::sf(se, ap, regSize1));
  inst.addElement(EflagsBuilder::zf(se, ap, regSize1));
}


void TestIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no test reg, mem available in x86 */
  TwoOperandsTemplate::stop(this->disas);
}


void TestIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
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
  expr << smt2lib::bvand(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createSE(expr);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::clearFlag(ap, ID_CF, "Clears carry flag"));
  inst.addElement(EflagsBuilder::clearFlag(ap, ID_OF, "Clears overflow flag"));
  inst.addElement(EflagsBuilder::pf(se, ap));
  inst.addElement(EflagsBuilder::sf(se, ap, writeSize));
  inst.addElement(EflagsBuilder::zf(se, ap, writeSize));
}


void TestIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint32_t          writeSize = std::get<2>(this->operands[0]);
  uint64_t          mem       = std::get<1>(this->operands[0]);
  uint64_t          reg       = std::get<1>(this->operands[1]);
  uint32_t          regSize   = std::get<2>(this->operands[1]);

  uint64_t          symReg    = ap.getRegSymbolicID(reg);
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
  expr << smt2lib::bvand(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createSE(expr);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::clearFlag(ap, ID_CF, "Clears carry flag"));
  inst.addElement(EflagsBuilder::clearFlag(ap, ID_OF, "Clears overflow flag"));
  inst.addElement(EflagsBuilder::pf(se, ap));
  inst.addElement(EflagsBuilder::sf(se, ap, writeSize));
  inst.addElement(EflagsBuilder::zf(se, ap, writeSize));
}


Inst *TestIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "TEST");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

