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



/*! \page py_SOLVER_page SOLVER
    \brief [**python api**] All information about the SOLVER Python namespace.

\tableofcontents

\section SOLVER_py_description Description
<hr>

The SOLVER namespace contains all kinds of solver status.

\section SOLVER_py_api Python API - Items of the SOLVER namespace
<hr>

- **SOLVER.OUTOFMEM**
- **SOLVER.SAT**
- **SOLVER.TIMEOUT**
- **SOLVER.UNKNOWN**
- **SOLVER.UNSAT**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initSolverNamespace(PyObject* solverDict) {
        PyDict_Clear(solverDict);

        xPyDict_SetItemString(solverDict, "OUTOFMEM", PyLong_FromUint32(triton::engines::solver::OUTOFMEM));
        xPyDict_SetItemString(solverDict, "SAT",      PyLong_FromUint32(triton::engines::solver::SAT));
        xPyDict_SetItemString(solverDict, "TIMEOUT",  PyLong_FromUint32(triton::engines::solver::TIMEOUT));
        xPyDict_SetItemString(solverDict, "UNKNOWN",  PyLong_FromUint32(triton::engines::solver::UNKNOWN));
        xPyDict_SetItemString(solverDict, "UNSAT",    PyLong_FromUint32(triton::engines::solver::UNSAT));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
