#include <iostream>
#include <sstream>
#include <stdexcept>

#include "XchgIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


XchgIRBuilder::XchgIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void XchgIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void XchgIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se1, *se2;
  std::stringstream expr1, expr2, op1, op2;
  uint64_t          reg1          = std::get<1>(this->operands[0]);
  uint64_t          reg2          = std::get<1>(this->operands[1]);
  uint64_t          symReg1       = ap.getRegSymbolicID(reg1);
  uint64_t          symReg2       = ap.getRegSymbolicID(reg2);
  uint32_t          regSize1      = std::get<2>(this->operands[0]);
  uint32_t          regSize2      = std::get<2>(this->operands[1]);
  uint64_t          tmpReg1Taint  = ap.isRegTainted(reg1);
  uint64_t          tmpReg2Taint  = ap.isRegTainted(reg2);

  /* Create the SMT semantic */
  if (symReg1 != UNSET)
    op1 << smt2lib::extract(regSize1, "#" + std::to_string(symReg1));
  else
    op1 << smt2lib::bv(ap.getRegisterValue(reg1), regSize1 * REG_SIZE);

  if (symReg2 != UNSET)
    op2 << smt2lib::extract(regSize2, "#" + std::to_string(symReg2));
  else
    op2 << smt2lib::bv(ap.getRegisterValue(reg2), regSize2 * REG_SIZE);

  // Final expr
  expr1 << op2.str();
  expr2 << op1.str();

  /* Create the symbolic element */
  se1 = ap.createRegSE(expr1, reg1);
  se2 = ap.createRegSE(expr2, reg2);

  /* Apply the taint */
  ap.setTaintReg(reg1, tmpReg2Taint);
  ap.setTaintReg(reg2, tmpReg1Taint);

  /* Add the symbolic element to the current inst */
  inst.addElement(se1);
  inst.addElement(se2);
}


void XchgIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se1, *se2;
  std::stringstream expr1, expr2, op1, op2;
  uint64_t          reg1          = std::get<1>(this->operands[0]);
  uint64_t          mem2          = std::get<1>(this->operands[1]);
  uint64_t          symReg1       = ap.getRegSymbolicID(reg1);
  uint64_t          symMem2       = ap.getMemSymbolicID(mem2);
  uint32_t          regSize1      = std::get<2>(this->operands[0]);
  uint32_t          memSize2      = std::get<2>(this->operands[1]);
  uint64_t          tmpReg1Taint  = ap.isRegTainted(reg1);
  uint64_t          tmpMem2Taint  = ap.isMemTainted(mem2);

  /* Create the SMT semantic */
  if (symReg1 != UNSET)
    op1 << smt2lib::extract(regSize1, "#" + std::to_string(symReg1));
  else
    op1 << smt2lib::bv(ap.getRegisterValue(reg1), regSize1 * REG_SIZE);

  if (symMem2 != UNSET)
    op2 << smt2lib::extract(memSize2, "#" + std::to_string(symMem2));
  else
    op2 << smt2lib::bv(ap.getMemValue(mem2, memSize2), memSize2 * REG_SIZE);

  // Final expr
  expr1 << op2.str();
  expr2 << op1.str();

  /* Create the symbolic element */
  se1 = ap.createRegSE(expr1, reg1);
  se2 = ap.createMemSE(expr2, mem2);

  /* Apply the taint */
  ap.setTaintReg(reg1, tmpMem2Taint);
  ap.setTaintMem(mem2, tmpReg1Taint);

  /* Add the symbolic element to the current inst */
  inst.addElement(se1);
  inst.addElement(se2);
}


void XchgIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void XchgIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se1, *se2;
  std::stringstream expr1, expr2, op1, op2;
  uint64_t          mem1          = std::get<1>(this->operands[0]);
  uint64_t          reg2          = std::get<1>(this->operands[1]);
  uint64_t          symMem1       = ap.getMemSymbolicID(mem1);
  uint64_t          symReg2       = ap.getRegSymbolicID(reg2);
  uint32_t          memSize1      = std::get<2>(this->operands[0]);
  uint32_t          regSize2      = std::get<2>(this->operands[1]);
  uint64_t          tmpMem1Taint  = ap.isMemTainted(mem1);
  uint64_t          tmpReg2Taint  = ap.isRegTainted(reg2);

  /* Create the SMT semantic */
  if (symMem1 != UNSET)
    op1 << smt2lib::extract(memSize1, "#" + std::to_string(symMem1));
  else
    op1 << smt2lib::bv(ap.getMemValue(mem1, memSize1), memSize1 * REG_SIZE);

  if (symReg2 != UNSET)
    op2 << smt2lib::extract(regSize2, "#" + std::to_string(symReg2));
  else
    op2 << smt2lib::bv(ap.getRegisterValue(reg2), regSize2 * REG_SIZE);

  // Final expr
  expr1 << op2.str();
  expr2 << op1.str();

  /* Create the symbolic element */
  se1 = ap.createMemSE(expr1, mem1);
  se2 = ap.createRegSE(expr2, reg2);

  /* Apply the taint */
  ap.setTaintMem(mem1, tmpReg2Taint);
  ap.setTaintReg(reg2, tmpMem1Taint);

  /* Add the symbolic element to the current inst */
  inst.addElement(se1);
  inst.addElement(se2);
}


Inst *XchgIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "XCHG");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

