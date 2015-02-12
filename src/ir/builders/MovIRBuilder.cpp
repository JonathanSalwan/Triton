#include <iostream>
#include <sstream>
#include <stdexcept>

#include "MovIRBuilder.h"
#include "smt2lib_utils.h"


MovIRBuilder::MovIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {

}


std::stringstream *MovIRBuilder::regImm(const ContextHandler &ctxH) const {
  std::stringstream *expr = new std::stringstream();
  uint64_t regID = _operands[0].second;
  uint64_t imm = _operands[1].second;

  *expr << smt2lib::bv(imm, ctxH.getRegisterSize(regID));

  return expr;
}

std::stringstream *MovIRBuilder::regReg(const ContextHandler &ctxH) const {
  return nullptr;
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
