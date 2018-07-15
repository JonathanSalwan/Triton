//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/x86Specifications.hpp>



/*! \page py_PREFIX_page PREFIX
    \brief [**python api**] All information about the PREFIX python namespace.

\tableofcontents

\section PREFIX_py_description Description
<hr>

According to the CPU architecture, the PREFIX namespace contains all kinds of instruction prefixes.

\section PREFIX_py_api Python API - Items of the PREFIX namespace
<hr>

\subsection PREFIX_x86_py_api x86 and x86_64

- **PREFIX.INVALID**<br>
- **PREFIX.LOCK**<br>
- **PREFIX.REP**<br>
- **PREFIX.REPE**<br>
- **PREFIX.REPNE**<br>

*/


namespace triton {
  namespace bindings {
    namespace python {

#ifdef IS_PY3
      NAMESPACE_TYPE(PREFIX, PrefixNamespace)

      PyObject* initX86PrefixesNamespace() {
        PyType_Ready(&PrefixNamespace_Type);
        PyObject* prefixesDict = PrefixNamespace_Type.tp_dict;
#else
      void initX86PrefixesNamespace(PyObject* prefixesDict) {
        PyDict_Clear(prefixesDict);
#endif

        xPyDict_SetItemString(prefixesDict, "INVALID", PyLong_FromUint32(triton::arch::x86::ID_PREFIX_INVALID));
        xPyDict_SetItemString(prefixesDict, "LOCK",    PyLong_FromUint32(triton::arch::x86::ID_PREFIX_LOCK));
        xPyDict_SetItemString(prefixesDict, "REP",     PyLong_FromUint32(triton::arch::x86::ID_PREFIX_REP));
        xPyDict_SetItemString(prefixesDict, "REPE",    PyLong_FromUint32(triton::arch::x86::ID_PREFIX_REPE));
        xPyDict_SetItemString(prefixesDict, "REPNE",   PyLong_FromUint32(triton::arch::x86::ID_PREFIX_REPNE));
#ifdef IS_PY3
        return _PyObject_New(&PrefixNamespace_Type);
#endif
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
