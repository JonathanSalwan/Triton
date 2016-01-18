//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <python2.7/Python.h>

#include <operandInterface.hpp>
#include <pythonBindings.hpp>
#include <pythonUtils.hpp>
#include <symbolicOptimization.hpp>



/*! \page py_OPTIMIZATION_page OPTIMIZATION
    \brief [**python api**] All information about the OPTIMIZATION python namespace.

\tableofcontents

\section OPTIMIZATION_py_description Description
<hr>

The OPTIMIZATION namespace contains all kinds of symbolic optimization.

\section OPTIMIZATION_py_api Python API - Items of the OPTIMIZATION namespace
<hr>

- **OPTIMIZATION.ONLY_ON_TAINTED**<br>
Enabled, Triton will perform symbolic execution only on tainted instructions.

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initSymOptiNamespace(PyObject* symOptiDict) {
        PyDict_SetItemString(symOptiDict, "ONLY_ON_TAINTED", PyLong_FromUint(triton::engines::symbolic::ONLY_ON_TAINTED));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
