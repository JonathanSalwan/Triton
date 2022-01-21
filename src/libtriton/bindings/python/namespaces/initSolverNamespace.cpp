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

- **SOLVER.Z3**
- **SOLVER.BITWUZLA**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initSolverNamespace(PyObject* solverDict) {
        PyDict_Clear(solverDict);

        #if defined(TRITON_Z3_INTERFACE)
        xPyDict_SetItemString(solverDict, "Z3", PyLong_FromUint32(triton::engines::solver::SOLVER_Z3));
        #endif
        #if defined(TRITON_BITWUZLA_INTERFACE)
        xPyDict_SetItemString(solverDict, "BITWUZLA", PyLong_FromUint32(triton::engines::solver::SOLVER_BITWUZLA));
        #endif
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
