/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_TRACE_H
#define TRITON_TRACE_H

#include "TritonTypes.h"

#include <iostream>
#include <ostream>
#include <list>

#include "SymbolicEngine.h"
#include "Inst.h"

/* Trace of a run */
class Trace {

  private:
    /* A trace contains a list of instruction */
    std::list<Inst *> instructions;

  public:
    Trace();
    ~Trace();

    /* Add an instruction into the Trace */
    void addInstruction(Inst *instruction);

    /* Returns the last instruction added */
    Inst *getLastInstruction(void);

    /* Get all instructions from the Trace */
    std::list<Inst *> &getInstructions();
};

#endif /* !_TRACE_H_ */

