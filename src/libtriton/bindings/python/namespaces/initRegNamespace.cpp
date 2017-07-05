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
#include <triton/architecture.hpp>
#include <triton/coreUtils.hpp>



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

        triton::arch::Architecture x86;
        triton::arch::Architecture x8664;

        x86.setArchitecture(triton::arch::ARCH_X86);
        x8664.setArchitecture(triton::arch::ARCH_X86_64);

        PyObject* x86RegistersDict      = xPyDict_New();
        PyObject* x86RegistersDictClass = xPyClass_New(nullptr, x86RegistersDict, xPyString_FromString("X86"));
        PyDict_SetItemString(registersDict, "X86", x86RegistersDictClass);

        // Init X86 REG namespace
        for (const auto& reg : x86.getAllRegisters()) {
          /* Duplicate register name */
          std::string n(reg.second.getName());
          /* To upper... */
          triton::utils::toupper(n);
          /* Add the to Python dict */
          PyDict_SetItemString(x86RegistersDict, n.c_str(), PyRegister(reg.second));
        }

        PyObject* x8664RegistersDict      = xPyDict_New();
        PyObject* x8664RegistersDictClass = xPyClass_New(nullptr, x8664RegistersDict, xPyString_FromString("X86_64"));
        PyDict_SetItemString(registersDict, "X86_64", x8664RegistersDictClass);

        // Init X86_64 REG namespace
        for (const auto& reg : x8664.getAllRegisters()) {
          /* Duplicate register name */
          std::string n(reg.second.getName());
          /* To upper... */
          triton::utils::toupper(n);
          /* Add the to Python dict */
          PyDict_SetItemString(x8664RegistersDict, n.c_str(), PyRegister(reg.second));
        }
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
