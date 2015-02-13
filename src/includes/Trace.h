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
    std::list<Inst *> instructions;

  public:
    // TODO: it will be replace by the Facade: AnalysisProcessor
    /* Symbolic Engine */
    SymbolicEngine symbolicEngine;

    Trace();
    ~Trace();

    void addInstruction(Inst *instruction);
    std::list<Inst *> &getInstructions();

    // Display the trace: all the instructions and their expressions.
    void display(std::ostream &os = std::cout);
};

#endif /* !_TRACE_H_ */

