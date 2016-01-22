//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <api.hpp>
#include <cpuSize.hpp>
#include <pythonBindings.hpp>
#include <pythonUtils.hpp>

#ifdef __unix__
  #include <python2.7/Python.h>
#elif _WIN32
  #include <Python.h>
#endif



/*! \page py_CPUSIZE_page CPUSIZE
    \brief [**python api**] All information about the CPUSIZE python namespace.

\tableofcontents

\section CPUSIZE_py_description Description
<hr>

According to the CPU architecture, the CPUSIZE namespace contains all kinds of size.

\section CPUSIZE_py_api Python API - Items of the CPUSIZE namespace
<hr>

- **CPUSIZE.BYTE**<br>
Returns `1`

- **CPUSIZE.BYTE_BIT**<br>
Returns `8`

- **CPUSIZE.WORD**<br>
Returns `2`

- **CPUSIZE.WORD_BIT**<br>
Returns `16`

- **CPUSIZE.DWORD**<br>
Returns `4`

- **CPUSIZE.DWORD_BIT**<br>
Returns `32`

- **CPUSIZE.QWORD**<br>
Returns `8`

- **CPUSIZE.QWORD_BIT**<br>
Returns `64`

- **CPUSIZE.DQWORD**<br>
Returns `16`

- **CPUSIZE.DQWORD_BIT**<br>
Returns `128`

- **CPUSIZE.REG**<br>
Returns the max register's size according to your CPU architecture.

- **CPUSIZE.REG_BIT**<br>
Returns the max register's size (in bit) according to your CPU architecture.

- **CPUSIZE.SSE_REG**<br>
Returns `CPUSIZE.DQWORD`

- **CPUSIZE.SSE_REG_BIT**<br>
Returns `CPUSIZE.DQWORD_BIT`

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initCpuSizeNamespace(void) {

        if (!triton::bindings::python::initialized)
          return;

        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "BYTE",        PyLong_FromUint(BYTE_SIZE));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "BYTE_BIT",    PyLong_FromUint(BYTE_SIZE_BIT));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "WORD",        PyLong_FromUint(WORD_SIZE));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "WORD_BIT",    PyLong_FromUint(WORD_SIZE_BIT));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "DWORD",       PyLong_FromUint(DWORD_SIZE));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "DWORD_BIT",   PyLong_FromUint(DWORD_SIZE_BIT));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "QWORD",       PyLong_FromUint(QWORD_SIZE));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "QWORD_BIT",   PyLong_FromUint(QWORD_SIZE_BIT));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "DQWORD",      PyLong_FromUint(DQWORD_SIZE));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "DQWORD_BIT",  PyLong_FromUint(DQWORD_SIZE_BIT));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "REG",         PyLong_FromUint(triton::api.cpuRegSize()));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "REG_BIT",     PyLong_FromUint(triton::api.cpuRegBitSize()));

      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
