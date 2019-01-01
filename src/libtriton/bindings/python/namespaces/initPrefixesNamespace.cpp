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

- **PREFIX.X86.INVALID**<br>
- **PREFIX.X86.LOCK**<br>
- **PREFIX.X86.REP**<br>
- **PREFIX.X86.REPE**<br>
- **PREFIX.X86.REPNE**<br>

*/


namespace triton {
  namespace bindings {
    namespace python {

      void initPrefixesNamespace(PyObject* prefixesDict) {
        PyDict_Clear(prefixesDict);

        PyObject* x86PrefixesDict      = xPyDict_New();
        PyObject* x86PrefixesDictClass = xPyClass_New(nullptr, x86PrefixesDict, xPyString_FromString("X86"));
        xPyDict_SetItemString(prefixesDict, "X86", x86PrefixesDictClass);

        xPyDict_SetItemString(x86PrefixesDict, "INVALID", PyLong_FromUint32(triton::arch::x86::ID_PREFIX_INVALID));
        xPyDict_SetItemString(x86PrefixesDict, "LOCK",    PyLong_FromUint32(triton::arch::x86::ID_PREFIX_LOCK));
        xPyDict_SetItemString(x86PrefixesDict, "REP",     PyLong_FromUint32(triton::arch::x86::ID_PREFIX_REP));
        xPyDict_SetItemString(x86PrefixesDict, "REPE",    PyLong_FromUint32(triton::arch::x86::ID_PREFIX_REPE));
        xPyDict_SetItemString(x86PrefixesDict, "REPNE",   PyLong_FromUint32(triton::arch::x86::ID_PREFIX_REPNE));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
