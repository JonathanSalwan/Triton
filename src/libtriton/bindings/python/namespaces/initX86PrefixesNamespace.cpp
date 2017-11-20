//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
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

      void initX86PrefixesNamespace(PyObject* prefixesDict) {
        PyDict_Clear(prefixesDict);

        PyDict_SetItemStringSteal(prefixesDict, "INVALID", PyLong_FromUint32(triton::arch::x86::ID_PREFIX_INVALID));
        PyDict_SetItemStringSteal(prefixesDict, "LOCK",    PyLong_FromUint32(triton::arch::x86::ID_PREFIX_LOCK));
        PyDict_SetItemStringSteal(prefixesDict, "REP",     PyLong_FromUint32(triton::arch::x86::ID_PREFIX_REP));
        PyDict_SetItemStringSteal(prefixesDict, "REPE",    PyLong_FromUint32(triton::arch::x86::ID_PREFIX_REPE));
        PyDict_SetItemStringSteal(prefixesDict, "REPNE",   PyLong_FromUint32(triton::arch::x86::ID_PREFIX_REPNE));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
