
#ifndef   SOLVERENGINE_H
#define   SOLVERENGINE_H

#include <cstdlib>
#include <string>

#include <z3++.h>

#include "Registers.h"
#include "Smodel.h"
#include "SymbolicEngine.h"
#include "TritonTypes.h"


class SolverEngine
{
  private:
    SymbolicEngine *symEngine;

  public:
    std::list<Smodel> getModel(std::string expr);

    SolverEngine(SymbolicEngine *sym);
    ~SolverEngine();
};


#endif     /* !__SOLVERENGINE_H__ */

