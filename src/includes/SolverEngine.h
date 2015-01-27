
#ifndef   __SOLVERENGINE_H__
#define   __SOLVERENGINE_H__

#include <cstdlib>
#include <stdint.h>
#include <string>

#include <z3++.h>

#include "registers.h"
#include "SymbolicEngine.h"


class SolverEngine
{
  private:
    SymbolicEngine      *symEngine;
    std::stringstream   formula;
    z3::context         *ctx;
    z3::solver          *solver;

  public:
    std::string         getFormula();
    void                displayModel();
    void                solveFromID(uint64_t id);
    z3::model           getModel();

    SolverEngine(SymbolicEngine *sym);
    ~SolverEngine();
};


#endif     /* !__SOLVERENGINE_H__ */

