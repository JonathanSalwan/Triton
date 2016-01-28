//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <operandInterface.hpp>
#include <pythonBindings.hpp>
#include <pythonUtils.hpp>
#include <symbolicOptimization.hpp>

#ifdef __unix__
  #include <python2.7/Python.h>
#elif _WIN32
  #include <Python.h>
#endif



/*! \page py_OPTIMIZATION_page OPTIMIZATION
    \brief [**python api**] All information about the OPTIMIZATION python namespace.

\tableofcontents

\section OPTIMIZATION_py_description Description
<hr>

The OPTIMIZATION namespace contains all kinds of symbolic optimization.

\section OPTIMIZATION_py_api Python API - Items of the OPTIMIZATION namespace
<hr>

- **OPTIMIZATION.ALIGNED_MEMORY**<br>
Enabled, Triton will keep a map of aligned memory to reduce the symbolic memory explosion of `LOAD` and `STORE` acceess.

- **OPTIMIZATION.AST_SUMMARIES**<br>
Enabled, Triton will record all AST nodes into several maps and try to return node already allocated instead of allocate twice the same node.

- **OPTIMIZATION.ONLY_ON_TAINTED**<br>
Enabled, Triton will perform symbolic execution only on tainted instructions.

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initSymOptiNamespace(PyObject* symOptiDict) {
        PyDict_SetItemString(symOptiDict, "ALIGNED_MEMORY",   PyLong_FromUint(triton::engines::symbolic::ALIGNED_MEMORY));
        PyDict_SetItemString(symOptiDict, "AST_SUMMARIES",    PyLong_FromUint(triton::engines::symbolic::AST_SUMMARIES));
        PyDict_SetItemString(symOptiDict, "ONLY_ON_TAINTED",  PyLong_FromUint(triton::engines::symbolic::ONLY_ON_TAINTED));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
