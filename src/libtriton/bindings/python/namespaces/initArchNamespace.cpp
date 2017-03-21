//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/architecture.hpp>
#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>



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
        PyDict_SetItemString(archDict, "X86",     PyLong_FromUint32(triton::arch::ARCH_X86));
        PyDict_SetItemString(archDict, "X86_64",  PyLong_FromUint32(triton::arch::ARCH_X86_64));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
