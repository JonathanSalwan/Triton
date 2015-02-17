#include "MovsxIRBuilder.h"

MovsxIRBuilder::MovsxIRBuilder(uint64_t address, const std::string &disassembly):
  MovIRBuilder(address, disassembly) {
    this->extender = &smt2lib::sx;
}
