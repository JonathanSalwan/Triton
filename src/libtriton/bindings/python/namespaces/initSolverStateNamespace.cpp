//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/solverEnums.hpp>



/*! \page py_SOLVER_STATE_page SOLVER_STATE
    \brief [**python api**] All information about the SOLVER_STATE Python namespace.

\tableofcontents

\section SOLVER_STATE_py_description Description
<hr>

The SOLVER_STATE namespace contains all kinds of solver status.

\section SOLVER_STATE_py_api Python API - Items of the SOLVER_STATE namespace
<hr>

- **SOLVER_STATE.OUTOFMEM**
- **SOLVER_STATE.SAT**
- **SOLVER_STATE.TIMEOUT**
- **SOLVER_STATE.UNKNOWN**
- **SOLVER_STATE.UNSAT**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initSolverStateNamespace(PyObject* solverStateDict) {
        PyDict_Clear(solverStateDict);

        xPyDict_SetItemString(solverStateDict, "OUTOFMEM", PyLong_FromUint32(triton::engines::solver::OUTOFMEM));
        xPyDict_SetItemString(solverStateDict, "SAT",      PyLong_FromUint32(triton::engines::solver::SAT));
        xPyDict_SetItemString(solverStateDict, "TIMEOUT",  PyLong_FromUint32(triton::engines::solver::TIMEOUT));
        xPyDict_SetItemString(solverStateDict, "UNKNOWN",  PyLong_FromUint32(triton::engines::solver::UNKNOWN));
        xPyDict_SetItemString(solverStateDict, "UNSAT",    PyLong_FromUint32(triton::engines::solver::UNSAT));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
