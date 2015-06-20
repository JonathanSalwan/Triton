
#ifndef   SOLVERENGINE_H
#define   SOLVERENGINE_H

#include <cstdlib>
#include "TritonTypes.h"
#include <string>

#include <z3++.h>

#include "Registers.h"
#include "SymbolicEngine.h"


class SolverEngine
{
  private:
    SymbolicEngine *symEngine;

  public:
    std::list< std::pair<std::string, unsigned long long> > getModel(std::string expr);

    SolverEngine(SymbolicEngine *sym);
    ~SolverEngine();
};


#endif     /* !__SOLVERENGINE_H__ */

