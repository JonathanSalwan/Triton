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

#ifdef IS_PY3
      NAMESPACE_TYPE(MODE, ModeNamespace)

      PyObject* initModeNamespace() {
        PyType_Ready(&ModeNamespace_Type);
        PyObject *modeDict = ModeNamespace_Type.tp_dict;
#else
      void initModeNamespace(PyObject* modeDict) {
#endif
        xPyDict_SetItemString(modeDict, "ALIGNED_MEMORY",         PyLong_FromUint32(triton::modes::ALIGNED_MEMORY));
        xPyDict_SetItemString(modeDict, "ONLY_ON_SYMBOLIZED",     PyLong_FromUint32(triton::modes::ONLY_ON_SYMBOLIZED));
        xPyDict_SetItemString(modeDict, "ONLY_ON_TAINTED",        PyLong_FromUint32(triton::modes::ONLY_ON_TAINTED));
        xPyDict_SetItemString(modeDict, "PC_TRACKING_SYMBOLIC",   PyLong_FromUint32(triton::modes::PC_TRACKING_SYMBOLIC));
#ifdef IS_PY3
        return _PyObject_New(&ModeNamespace_Type);
#endif
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
