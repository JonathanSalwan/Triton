//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/modes.hpp>



/*! \page py_MODE_page MODE
    \brief [**python api**] All information about the MODE Python namespace.

\tableofcontents

\section MODE_py_description Description
<hr>

The MODE namespace contains all kinds of modes.

\subsection MODE_py_example Example

~~~~~~~~~~~~~{.py}
>>> setMode(MODE.ONLY_ON_TAINTED, True)
~~~~~~~~~~~~~

\section MODE_py_api Python API - Items of the MODE namespace
<hr>

- **MODE.ALIGNED_MEMORY**<br>
Enabled, Triton will keep a map of aligned memory to reduce the symbolic memory explosion of `LOAD` and `STORE` accesses.

- **MODE.AST_OPTIMIZATIONS**<br>
Enabled, Triton will reduces the depth of the trees using classical arithmetic optimisations.

- **MODE.CONCRETIZE_UNDEFINED_REGISTERS**<br>
Enabled, Triton will concretize every register tagged as undefined (see #750).

- **MODE.ITERATIVE_GC**<br>
Enabled, Triton will use an iterative mechanism to release garbage collected nodes. This option
may avoid stack overflow during the release of shared_ptr but impact (a little bit) the performance.

- **MODE.ONLY_ON_SYMBOLIZED**<br>
Enabled, Triton will perform symbolic execution only on symbolized expressions.

- **MODE.ONLY_ON_TAINTED**<br>
Enabled, Triton will perform symbolic execution only on tainted instructions.

- **MODE.PC_TRACKING_SYMBOLIC**<br>
Enabled, Triton will track path constraints only if they are symbolized. This mode is enabled by default.

- **MODE.SYMBOLIZE_INDEX_ROTATION**<br>
Enabled, Triton will symbolize the index of rotation for `bvror` and `bvrol` nodes. This mode increases the complexity of solving.

- **MODE.TAINT_THROUGH_POINTERS**<br>
Enabled, the taint is spread if an index pointer is already tainted (see #725).
*/



namespace triton {
  namespace bindings {
    namespace python {

      void initModeNamespace(PyObject* modeDict) {
        xPyDict_SetItemString(modeDict, "ALIGNED_MEMORY",                 PyLong_FromUint32(triton::modes::ALIGNED_MEMORY));
        xPyDict_SetItemString(modeDict, "AST_OPTIMIZATIONS",              PyLong_FromUint32(triton::modes::AST_OPTIMIZATIONS));
        xPyDict_SetItemString(modeDict, "CONCRETIZE_UNDEFINED_REGISTERS", PyLong_FromUint32(triton::modes::CONCRETIZE_UNDEFINED_REGISTERS));
        xPyDict_SetItemString(modeDict, "ITERATIVE_GC",                   PyLong_FromUint32(triton::modes::ITERATIVE_GC));
        xPyDict_SetItemString(modeDict, "ONLY_ON_SYMBOLIZED",             PyLong_FromUint32(triton::modes::ONLY_ON_SYMBOLIZED));
        xPyDict_SetItemString(modeDict, "ONLY_ON_TAINTED",                PyLong_FromUint32(triton::modes::ONLY_ON_TAINTED));
        xPyDict_SetItemString(modeDict, "PC_TRACKING_SYMBOLIC",           PyLong_FromUint32(triton::modes::PC_TRACKING_SYMBOLIC));
        xPyDict_SetItemString(modeDict, "SYMBOLIZE_INDEX_ROTATION",       PyLong_FromUint32(triton::modes::SYMBOLIZE_INDEX_ROTATION));
        xPyDict_SetItemString(modeDict, "TAINT_THROUGH_POINTERS",         PyLong_FromUint32(triton::modes::TAINT_THROUGH_POINTERS));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
