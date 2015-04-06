#include "MovzxIRBuilder.h"

MovzxIRBuilder::MovzxIRBuilder(uint64_t address, const std::string &disassembly):
  MovIRBuilder(address, disassembly) {
    this->extender = &smt2lib::zx;
}


void MovzxIRBuilder::regImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}

void MovzxIRBuilder::memImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}

void MovzxIRBuilder::memReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}
