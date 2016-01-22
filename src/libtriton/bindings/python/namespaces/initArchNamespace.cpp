//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <architecture.hpp>
#include <pythonBindings.hpp>
#include <pythonUtils.hpp>

#ifdef __unix__
  #include <python2.7/Python.h>
#elif _WIN32
  #include <Python.h>
#endif



/*! \page py_ARCH_page ARCH
    \brief [**python api**] All information about the ARCH python namespace.

\tableofcontents

\section ARCH_py_description Description
<hr>

The ARCH namespace contains all kinds of architecture supported by Triton.

\section ARCH_py_api Python API - Items of the ARCH namespace
<hr>

- **ARCH.X86**
- **ARCH.X86_64**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initArchNamespace(PyObject* archDict) {

        PyDict_SetItemString(archDict, "X86", PyLong_FromUint(triton::arch::ARCH_X86));
        #if defined(__x86_64__) || defined(_M_X64)
        PyDict_SetItemString(archDict, "X86_64", PyLong_FromUint(triton::arch::ARCH_X86_64));
        #endif

      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
