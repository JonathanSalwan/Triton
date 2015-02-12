
#ifndef   __SOLVERENGINE_H__
#define   __SOLVERENGINE_H__

#include <cstdlib>
#include <stdint.h>
#include <string>

#include <z3++.h>

#include "Registers.h"
#include "SymbolicEngine.h"


class SolverEngine
{
  private:
    SymbolicEngine      *symEngine;
    std::stringstream   formula;
    z3::context         *ctx;
    z3::solver          *solver;
    z3::check_result    checkResult;

  public:
    std::string         getFormula();
    void                displayModel();
    void                solveFromID(uint64_t id);
    z3::model           getModel();
    z3::check_result    getCheckResult();

    SolverEngine(SymbolicEngine *sym);
    ~SolverEngine();
};


#endif     /* !__SOLVERENGINE_H__ */

