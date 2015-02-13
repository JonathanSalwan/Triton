#include <iostream>
#include <sstream>
#include <stdexcept>

#include "MovIRBuilder.h"
#include "SMT2Lib.h"
#include "SymbolicEngine.h"


MovIRBuilder::MovIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {

}


void MovIRBuilder::regImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicEngine &symEngine = ap.getSymbolicEngine();
  std::stringstream expr;
  uint64_t          reg = std::get<1>(_operands[0]);
  uint64_t          imm = std::get<1>(_operands[1]);

  expr << smt2lib::bv(imm, ctxH.getRegisterSize(reg));

  SymbolicElement *symElement = symEngine.newSymbolicElement(expr);
  symEngine.symbolicReg[ctxH.translateRegID(reg)] = symElement->getID();

  inst.addElement(symElement);
}


void MovIRBuilder::regReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicEngine &symEngine = ap.getSymbolicEngine();
  std::stringstream expr;
  uint64_t          reg1 = std::get<1>(_operands[0]);
  uint64_t          reg2 = std::get<1>(_operands[1]);

  if (symEngine.symbolicReg[ctxH.translateRegID(reg2)] != UNSET)
    expr << "#" << std::dec << symEngine.symbolicReg[ctxH.translateRegID(reg2)];
  else
    expr << smt2lib::bv(ctxH.getRegisterValue(reg2), ctxH.getRegisterSize(reg1));

  SymbolicElement *symElement = symEngine.newSymbolicElement(expr);
  symEngine.symbolicReg[ctxH.translateRegID(reg1)] = symElement->getID();

  inst.addElement(symElement);
}


void MovIRBuilder::regMem(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicEngine &symEngine = ap.getSymbolicEngine();
  std::stringstream expr;
  uint32_t          readSize = std::get<2>(_operands[1]);
  uint64_t          mem      = std::get<1>(_operands[1]);
  uint64_t          reg      = std::get<1>(_operands[0]);

  if (symEngine.isMemoryReference(mem) != UNSET)
    expr << "#" << std::dec << symEngine.isMemoryReference(mem);
  else
    expr << smt2lib::bv(ctxH.getMemoryValue(mem, readSize), readSize);

  SymbolicElement *symElement = symEngine.newSymbolicElement(expr);
  symEngine.symbolicReg[ctxH.translateRegID(reg)] = symElement->getID();

  inst.addElement(symElement);
}


void MovIRBuilder::memImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicEngine &symEngine = ap.getSymbolicEngine();
  std::stringstream expr;
  uint32_t          writeSize = std::get<2>(_operands[0]);
  uint64_t          mem       = std::get<1>(_operands[0]);
  uint64_t          imm       = std::get<1>(_operands[1]);

  expr << smt2lib::bv(imm, writeSize);

  SymbolicElement *symElement = symEngine.newSymbolicElement(expr);
  symEngine.addMemoryReference(mem, symElement->getID());

  inst.addElement(symElement);
}


void MovIRBuilder::memReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicEngine &symEngine(ap.getSymbolicEngine());
  std::stringstream expr;
  uint32_t          writeSize = std::get<2>(_operands[0]);
  uint64_t          mem       = std::get<1>(_operands[0]);
  uint64_t          reg       = std::get<1>(_operands[1]);

  if (symEngine.symbolicReg[ctxH.translateRegID(reg)] != UNSET)
    expr << "#" << std::dec << symEngine.symbolicReg[ctxH.translateRegID(reg)];
  else
    expr << smt2lib::bv(ctxH.getRegisterValue(reg), writeSize);

  SymbolicElement *symElement = symEngine.newSymbolicElement(expr);
  symEngine.addMemoryReference(mem, symElement->getID());

  inst.addElement(symElement);
}


Inst *MovIRBuilder::process(const ContextHandler &ctxH, AnalysisProcessor &ap) const {
  checkSetup();

  Inst *inst = new Inst(_address, _disas);

  try {
    templateMethod(ctxH, ap, *inst, _operands, "MOV");
  }
  catch (std::exception &e) {
    delete inst;
    throw e;
  }

  return inst;
}

