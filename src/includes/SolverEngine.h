
#ifndef   __SOLVERENGINE_H__
#define   __SOLVERENGINE_H__

#include <z3++.h>

#include "pin.H"
#include "triton.h"
#include "SymbolicEngine.h"

/* decl */
std::string     smt2lib_bv(UINT64 value, UINT64 size);
std::string     smt2lib_declare(UINT64 idSymVar, UINT64 BitVecSize);
std::string     smt2lib_extract(UINT64 regSize);


class SolverEngine
{
  private:
    SymbolicEngine      *symEngine;
    std::stringstream   formula;
    z3::solver          *solver;
    z3::context         *ctx;

  public:
    VOID                solveFromID(UINT64 id);
    VOID                displayModel();
    z3::model           getModel();
    std::string         getFormula();

    SolverEngine(SymbolicEngine *sym);
    ~SolverEngine();
};


#endif     /* !__SOLVERENGINE_H__ */

