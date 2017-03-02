//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/api.hpp>
#include <triton/cpuSize.hpp>
#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>



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

- **CPUSIZE.QQWORD**<br>
Returns `32`

- **CPUSIZE.QQWORD_BIT**<br>
Returns `256`

- **CPUSIZE.DQQWORD**<br>
Returns `64`

- **CPUSIZE.DQQWORD_BIT**<br>
Returns `512`

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initCpuSizeNamespace(void) {
        if (!triton::bindings::python::initialized)
          return;

        PyDict_Clear(triton::bindings::python::cpuSizeDict);

        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "BYTE",        PyLong_FromUint32(BYTE_SIZE));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "BYTE_BIT",    PyLong_FromUint32(BYTE_SIZE_BIT));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "WORD",        PyLong_FromUint32(WORD_SIZE));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "WORD_BIT",    PyLong_FromUint32(WORD_SIZE_BIT));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "DWORD",       PyLong_FromUint32(DWORD_SIZE));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "DWORD_BIT",   PyLong_FromUint32(DWORD_SIZE_BIT));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "QWORD",       PyLong_FromUint32(QWORD_SIZE));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "QWORD_BIT",   PyLong_FromUint32(QWORD_SIZE_BIT));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "DQWORD",      PyLong_FromUint32(DQWORD_SIZE));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "DQWORD_BIT",  PyLong_FromUint32(DQWORD_SIZE_BIT));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "QQWORD",      PyLong_FromUint32(QQWORD_SIZE));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "QQWORD_BIT",  PyLong_FromUint32(QQWORD_SIZE_BIT));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "DQQWORD",     PyLong_FromUint32(DQQWORD_SIZE));
        PyDict_SetItemString(triton::bindings::python::cpuSizeDict, "DQQWORD_BIT", PyLong_FromUint32(DQQWORD_SIZE_BIT));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
