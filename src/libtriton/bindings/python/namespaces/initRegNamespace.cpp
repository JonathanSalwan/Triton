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


/* setup doctest context

>>> from triton import ARCH, TritonContext, REG
>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)

*/

/*! \page py_REG_page REG
    \brief [**python api**] All information about the REG python namespace.

\tableofcontents

\section REG_py_description Description
<hr>

According to the CPU architecture, the REG namespace contains all enums of register.
It's possible to create a \ref py_Register_page from a register id using `getRegister`
like this:

~~~~~~~~~~~~~{.py}
>>> ah = ctxt.getRegister(REG.X86_64.AH)
>>> print ah
ah:8 bv[15..8]

~~~~~~~~~~~~~

Note that creating a \ref py_TritonContext_page, you can directly access to constructed
\ref py_Register_page according to your defined architecture.

~~~~~~~~~~~~~{.py}
>>> ctxt.setArchitecture(ARCH.X86_64)
>>> print ctxt.registers.zmm1
zmm1:512 bv[511..0]

~~~~~~~~~~~~~

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
