#include <iostream>
#include <sstream>
#include <stdexcept>

#include "MovIRBuilder.h"
#include "smt2lib_utils.h"
#include "SymbolicEngine.h"

extern SymbolicEngine *symEngine;


MovIRBuilder::MovIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {

}


std::stringstream *MovIRBuilder::regImm(const ContextHandler &ctxH) const {
  std::stringstream expr;
  uint64_t          reg = _operands[0].second;
  uint64_t          imm = _operands[1].second;

  expr << smt2lib::bv(imm, ctxH.getRegisterSize(reg));

  SymbolicElement *symElement = symEngine->newSymbolicElement(expr);
  symEngine->symbolicReg[reg] = symElement->getID();

  return symElement->getExpression();
}


std::stringstream *MovIRBuilder::regReg(const ContextHandler &ctxH) const {
  std::stringstream expr;
  uint64_t          reg1 = _operands[0].second;
  uint64_t          reg2 = _operands[1].second;

  if (symEngine->symbolicReg[reg2] != UNSET)
    expr << "#" << std::dec << symEngine->symbolicReg[reg2];
  else
    expr << smt2lib::bv(ctxH.getRegisterValue(reg2), ctxH.getRegisterSize(reg1));

  SymbolicElement *symElement = symEngine->newSymbolicElement(expr);
  symEngine->symbolicReg[reg1] = symElement->getID();

  return symElement->getExpression();
}


std::stringstream *MovIRBuilder::regMem(const ContextHandler &ctxH) const {
  return nullptr;
}


std::stringstream *MovIRBuilder::memImm(const ContextHandler &ctxH) const {
  return nullptr;
}


std::stringstream *MovIRBuilder::memReg(const ContextHandler &ctxH) const {
  return nullptr;
}


std::stringstream *MovIRBuilder::process(const ContextHandler &ctxH) const {
  checkSetup();

  return templateMethod(ctxH, _operands, "MOV");
}
