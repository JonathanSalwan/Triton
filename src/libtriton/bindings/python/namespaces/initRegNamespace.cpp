//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>



/*! \page py_REG_page REG
    \brief [**python api**] All information about the REG python namespace.

\tableofcontents

\section REG_py_description Description
<hr>

According to the CPU architecture, the REG namespace contains all kinds of register.

\section REG_py_api Python API - Items of the REG namespace
<hr>

\subsection REG_X86_py_api x86 registers

\include x86_reg

\subsection REG_X8664_py_api x86-64 registers

\include x8664_reg

*/

namespace triton {
  namespace bindings {
    namespace python {

      void initRegNamespace(PyObject* registersDict) {
        PyDict_Clear(registersDict);
        #define REG_SPEC(UPPER_NAME, LOWER_NAME, X86_64_UPPER, X86_64_LOWER, X86_64_PARENT, X86_UPPER, X86_LOWER, X86_PARENT, X86_AVAIL) \
          PyDict_SetItemString(registersDict, #UPPER_NAME, PyLong_FromUint32(triton::arch::ID_REG_##UPPER_NAME));
        #define REG_SPEC_NO_CAPSTONE REG_SPEC
        #include "triton/x86.spec"
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
