#include "MovzxIRBuilder.h"

MovzxIRBuilder::MovzxIRBuilder(uint64_t address, const std::string &disassembly):
  MovIRBuilder(address, disassembly) {
    this->extender = &smt2lib::zx;
}

static void stop(std::string disass)
{
  throw std::runtime_error("Error:"
                         + disass
                         + "is an invalid instruction. Wrong kind of operands.");
}

void MovzxIRBuilder::regImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  stop(this->_disas);
}

void MovzxIRBuilder::memImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  stop(this->_disas);
}

void MovzxIRBuilder::memReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  stop(this->_disas);
}
