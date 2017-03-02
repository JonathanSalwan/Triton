//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/modes.hpp>
#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>



/*! \page py_MODE_page MODE
    \brief [**python api**] All information about the MODE python namespace.

\tableofcontents

\section MODE_py_description Description
<hr>

The MODE namespace contains all kinds of mode.

\subsection MODE_py_example Example

~~~~~~~~~~~~~{.py}
>>> enableMode(MODE.ONLY_ON_TAINTED, True)
~~~~~~~~~~~~~

\section MODE_py_api Python API - Items of the MODE namespace
<hr>

- **MODE.ALIGNED_MEMORY**<br>
Enabled, Triton will keep a map of aligned memory to reduce the symbolic memory explosion of `LOAD` and `STORE` acceess.

- **MODE.AST_DICTIONARIES**<br>
Enabled, Triton will record all AST nodes into several dictionaries and try to return node already allocated instead of allocate twice the same node.

- **MODE.ONLY_ON_SYMBOLIZED**<br>
Enabled, Triton will perform symbolic execution only on symbolized expressions.

- **MODE.ONLY_ON_TAINTED**<br>
Enabled, Triton will perform symbolic execution only on tainted instructions.

- **MODE.PC_TRACKING_SYMBOLIC**<br>
Enabled, Triton will track path constraints only if they are symbolized. This mode is enabled by default.

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initModeNamespace(PyObject* modeDict) {
        PyDict_SetItemString(modeDict, "ALIGNED_MEMORY",         PyLong_FromUint32(triton::modes::ALIGNED_MEMORY));
        PyDict_SetItemString(modeDict, "AST_DICTIONARIES",       PyLong_FromUint32(triton::modes::AST_DICTIONARIES));
        PyDict_SetItemString(modeDict, "ONLY_ON_SYMBOLIZED",     PyLong_FromUint32(triton::modes::ONLY_ON_SYMBOLIZED));
        PyDict_SetItemString(modeDict, "ONLY_ON_TAINTED",        PyLong_FromUint32(triton::modes::ONLY_ON_TAINTED));
        PyDict_SetItemString(modeDict, "PC_TRACKING_SYMBOLIC",   PyLong_FromUint32(triton::modes::PC_TRACKING_SYMBOLIC));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
