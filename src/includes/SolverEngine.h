
#ifndef   __SOLVERENGINE_H__
#define   __SOLVERENGINE_H__

#include <cstdlib>
#include <cstdint>
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

