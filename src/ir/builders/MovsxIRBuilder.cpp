#include <stdexcept>

#include "MovsxIRBuilder.h"


MovsxIRBuilder::MovsxIRBuilder(uint64_t address, const std::string &disassembly):
  MovIRBuilder(address, disassembly)
{
  this->extender = &smt2lib::sx;
}

static void stop(std::string disass)
{
  throw std::runtime_error("Error:"
                         + disass
                         + "is an invalid instruction. Wrong kind of operands.");
}

void MovsxIRBuilder::regImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  stop(this->disas);
}

void MovsxIRBuilder::memImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  stop(this->disas);
}

void MovsxIRBuilder::memReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  stop(this->disas);
}
