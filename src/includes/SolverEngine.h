/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef SOLVERENGINE_H
#define SOLVERENGINE_H

#include <cstdlib>
#include <list>
#include <string>
#include <vector>

#include <z3++.h>

#include "Registers.h"
#include "SMT2Lib.h"
#include "Smodel.h"
#include "SymbolicEngine.h"
#include "TritonTypes.h"


class SolverEngine
{
  private:
    SymbolicEngine *symEngine;

  public:
    std::list<Smodel>               getModel(smt2lib::smtAstAbstractNode *node);
    std::vector<std::list<Smodel>>  getModels(smt2lib::smtAstAbstractNode *node, __uint limit);

    SolverEngine(SymbolicEngine *sym);
    ~SolverEngine();
};


#endif /* !__SOLVERENGINE_H__ */
#endif /* LIGHT_VERSION */

