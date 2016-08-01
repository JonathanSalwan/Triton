//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <pythonBindings.hpp>
#include <pythonUtils.hpp>
#include <symbolicOptimization.hpp>



/*! \page py_OPTIMIZATION_page OPTIMIZATION
    \brief [**python api**] All information about the OPTIMIZATION python namespace.

\tableofcontents

\section OPTIMIZATION_py_description Description
<hr>

The OPTIMIZATION namespace contains all kinds of symbolic optimization.

\subsection OPTIMIZATION_py_example Example

~~~~~~~~~~~~~{.py}
>>> enableSymbolicOptimization(OPTIMIZATION.ONLY_ON_TAINTED, True)
~~~~~~~~~~~~~

\section OPTIMIZATION_py_api Python API - Items of the OPTIMIZATION namespace
<hr>

- **OPTIMIZATION.ALIGNED_MEMORY**<br>
Enabled, Triton will keep a map of aligned memory to reduce the symbolic memory explosion of `LOAD` and `STORE` acceess.

- **OPTIMIZATION.AST_DICTIONARIES**<br>
Enabled, Triton will record all AST nodes into several dictionaries and try to return node already allocated instead of allocate twice the same node.

- **OPTIMIZATION.ONLY_ON_SYMBOLIZED**<br>
Enabled, Triton will perform symbolic execution only on symbolized expressions.

- **OPTIMIZATION.ONLY_ON_TAINTED**<br>
Enabled, Triton will perform symbolic execution only on tainted instructions.

- **OPTIMIZATION.PC_TRACKING_SYMBOLIC**<br>
Enabled, Triton will track path constraints only if they are symbolized. This optimization is enabled by default.

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initSymOptiNamespace(PyObject* symOptiDict) {
        PyDict_SetItemString(symOptiDict, "ALIGNED_MEMORY",         PyLong_FromUint32(triton::engines::symbolic::ALIGNED_MEMORY));
        PyDict_SetItemString(symOptiDict, "AST_DICTIONARIES",       PyLong_FromUint32(triton::engines::symbolic::AST_DICTIONARIES));
        PyDict_SetItemString(symOptiDict, "ONLY_ON_SYMBOLIZED",     PyLong_FromUint32(triton::engines::symbolic::ONLY_ON_SYMBOLIZED));
        PyDict_SetItemString(symOptiDict, "ONLY_ON_TAINTED",        PyLong_FromUint32(triton::engines::symbolic::ONLY_ON_TAINTED));
        PyDict_SetItemString(symOptiDict, "PC_TRACKING_SYMBOLIC",   PyLong_FromUint32(triton::engines::symbolic::PC_TRACKING_SYMBOLIC));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
