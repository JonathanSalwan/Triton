#include "MovzxIRBuilder.h"

MovzxIRBuilder::MovzxIRBuilder(uint64_t address, const std::string &disassembly):
  MovIRBuilder(address, disassembly) {
    this->extender = &smt2lib::zx;
}
