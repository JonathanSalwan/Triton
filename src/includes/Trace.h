#ifndef _TRACE_H_
#define _TRACE_H_

#include <cstdint>

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

    /* Get all instructions from the Trace */
    std::list<Inst *> &getInstructions();

    // Display the trace: all the instructions and their expressions.
    void save(std::stringstream &file);
};

#endif /* !_TRACE_H_ */

