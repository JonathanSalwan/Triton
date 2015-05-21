#include <iostream>
#include <sstream>
#include <stdexcept>

#include "OrpdIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


OrpdIRBuilder::OrpdIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void OrpdIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void OrpdIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint64_t          reg1     = this->operands[0].getValue();
  uint64_t          reg2     = this->operands[1].getValue();

  uint64_t          symReg1  = ap.getRegSymbolicID(reg1);
  uint64_t          symReg2  = ap.getRegSymbolicID(reg2);
  uint32_t          regSize1 = this->operands[0].getSize();
  uint32_t          regSize2 = this->operands[1].getSize();


  /* Create the SMT semantic */
  // OP_1
  if (symReg1 != UNSET)
    op1 << smt2lib::extract(regSize1, "#" + std::to_string(symReg1));
  else
    op1 << smt2lib::bv(ap.getSSERegisterValue(reg1), regSize1 * REG_SIZE);

  // OP_2
  if (symReg2 != UNSET)
    op2 << smt2lib::extract(regSize2, "#" + std::to_string(symReg2));
  else
    op2 << smt2lib::bv(ap.getSSERegisterValue(reg2), regSize1 * REG_SIZE);

  // Final expr
  expr << smt2lib::bvor(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg1);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg1, reg2);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void OrpdIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint32_t          readSize = this->operands[1].getSize();
  uint64_t          mem      = this->operands[1].getValue();
  uint64_t          reg      = this->operands[0].getValue();

  uint64_t          symReg   = ap.getRegSymbolicID(reg);
  uint64_t          symMem   = ap.getMemSymbolicID(mem);
  uint32_t          regSize  = this->operands[1].getSize();

  /* Create the SMT semantic */
  // OP_1
  if (symReg != UNSET)
    op1 << smt2lib::extract(regSize, "#" + std::to_string(symReg));
  else
    op1 << smt2lib::bv(ap.getSSERegisterValue(reg), readSize * REG_SIZE);

  // OP_2
  if (symMem != UNSET)
    op2 << "#" << std::dec << symMem;
  else
    op2 << smt2lib::bv(ap.getMemValue(mem, readSize), readSize * REG_SIZE);

  // Final expr
  expr << smt2lib::bvor(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg);

  /* Apply the taint */
  ap.aluSpreadTaintRegMem(se, reg, mem, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void OrpdIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void OrpdIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *OrpdIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "ORPD");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

