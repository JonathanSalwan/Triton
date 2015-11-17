/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <sstream>
#include <fstream>

#include <Colors.h>
#include <Trace.h>


Trace::Trace() {
}


Trace::~Trace() {
}


/* Add an instruction in the trace */
void Trace::addInstruction(Inst *instruction) {
  this->instructions.push_back(instruction);
}


/* Returns the last instuction added */
Inst *Trace::getLastInstruction(void) {
  return this->instructions.back();
}


/* Returns the instructions list in the trace */
std::list<Inst *> &Trace::getInstructions() {
  return this->instructions;
}

