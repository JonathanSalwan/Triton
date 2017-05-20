/* @file
 *
 *  Copyright (C) - Triton
 *
 *  This program is under the terms of the BSD License.
 */

#include <triton/pythonBindings.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>



/*! \page py_REG_page REG
    \brief [**python api**] All information about the REG python namespace.

\tableofcontents

\section REG_py_description Description
<hr>

According to the CPU architecture, the REG namespace contains all kinds of register.

\section REG_py_api Python API - Items of the REG namespace
<hr>

\subsection REG_X86_py_api x86 registers

\htmlinclude x86_reg

\subsection REG_X8664_py_api x86-64 registers

\htmlinclude x8664_reg

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initRegNamespace(PyObject* registersDict) {
        PyDict_Clear(registersDict);

        PyObject* x86RegistersDict      = xPyDict_New();
        PyObject* x86RegistersDictClass = xPyClass_New(nullptr, x86RegistersDict, xPyString_FromString("X86"));
        PyDict_SetItemString(registersDict, "X86", x86RegistersDictClass);

        // Init X86 REG namespace
        #define REG_SPEC(UPPER_NAME, LOWER_NAME, X86_64_UPPER, X86_64_LOWER, X86_64_PARENT, X86_UPPER, X86_LOWER, X86_PARENT, X86_AVAIL)  \
          if (X86_AVAIL)                                                                                                                  \
            PyDict_SetItemString(x86RegistersDict, #UPPER_NAME, PyLong_FromUint32(triton::arch::ID_REG_##UPPER_NAME));
        // Use REG not available in capstone as normal register
        #define REG_SPEC_NO_CAPSTONE REG_SPEC
        #include "triton/x86.spec"

        PyObject* x8664RegistersDict      = xPyDict_New();
        PyObject* x8664RegistersDictClass = xPyClass_New(nullptr, x8664RegistersDict, xPyString_FromString("X86_64"));
        PyDict_SetItemString(registersDict, "X86_64", x8664RegistersDictClass);

        // Init X86_64 REG namespace
        #define REG_SPEC(UPPER_NAME, LOWER_NAME, X86_64_UPPER, X86_64_LOWER, X86_64_PARENT, X86_UPPER, X86_LOWER, X86_PARENT, X86_AVAIL)  \
          PyDict_SetItemString(x8664RegistersDict, #UPPER_NAME, PyLong_FromUint32(triton::arch::ID_REG_##UPPER_NAME));
        // Use REG not available in capstone as normal register
        #define REG_SPEC_NO_CAPSTONE REG_SPEC
        #include "triton/x86.spec"
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
