#include <stdexcept>

#include "MovsxIRBuilder.h"


MovsxIRBuilder::MovsxIRBuilder(uint64_t address, const std::string &disassembly):
  MovIRBuilder(address, disassembly)
{
  this->extender = &smt2lib::sx;
}


void MovsxIRBuilder::regImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}

void MovsxIRBuilder::memImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}

void MovsxIRBuilder::memReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}
