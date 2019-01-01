//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/archEnums.hpp>



/*! \page py_EXTEND_page EXTEND
    \brief [**python api**] All information about the EXTEND python namespace.

\tableofcontents

\section EXTEND_py_description Description
<hr>

The EXTEND namespace contains all kinds of extend operand for AArch64.

\section EXTEND_py_api Python API - Items of the EXTEND namespace
<hr>

- **EXTEND.AARCH64.INVALID**<br>
Invalid extend operand.

- **EXTEND.AARCH64.UXTB**<br>
Extracts a byte (8-bit) value from a register and zero extends it to the size of the register.

- **EXTEND.AARCH64.UXTH**<br>
Extracts a halfword (16-bit) value from a register and zero extends it to the size of the register.

- **EXTEND.AARCH64.UXTW**<br>
Extracts a word (32-bit) value from a register and zero extends it to the size of the register

- **EXTEND.AARCH64.UXTX**<br>
Use the whole 64-bit register

- **EXTEND.AARCH64.SXTB**<br>
Extracts a byte (8-bit) value from a register and zero extends it to the size of the register

- **EXTEND.AARCH64.SXTH**<br>
Extracts a halfword (16-bit) value from a register and zero extends it to the size of the register

- **EXTEND.AARCH64.SXTW**<br>
Extracts a word (32-bit) value from a register and zero extends it to the size of the register

- **EXTEND.AARCH64.SXTX**<br>
Use the whole 64-bit register

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initExtendNamespace(PyObject* extendDict) {
        PyDict_Clear(extendDict);

        PyObject* aarch64ExtendDict      = xPyDict_New();
        PyObject* aarch64ExtendDictClass = xPyClass_New(nullptr, aarch64ExtendDict, xPyString_FromString("AARCH64"));
        xPyDict_SetItemString(extendDict, "AARCH64", aarch64ExtendDictClass);

        xPyDict_SetItemString(aarch64ExtendDict, "INVALID", PyLong_FromUint32(triton::arch::aarch64::ID_EXTEND_INVALID));
        xPyDict_SetItemString(aarch64ExtendDict, "UXTB",    PyLong_FromUint32(triton::arch::aarch64::ID_EXTEND_UXTB));
        xPyDict_SetItemString(aarch64ExtendDict, "UXTH",    PyLong_FromUint32(triton::arch::aarch64::ID_EXTEND_UXTH));
        xPyDict_SetItemString(aarch64ExtendDict, "UXTW",    PyLong_FromUint32(triton::arch::aarch64::ID_EXTEND_UXTW));
        xPyDict_SetItemString(aarch64ExtendDict, "UXTX",    PyLong_FromUint32(triton::arch::aarch64::ID_EXTEND_UXTX));
        xPyDict_SetItemString(aarch64ExtendDict, "SXTB",    PyLong_FromUint32(triton::arch::aarch64::ID_EXTEND_SXTB));
        xPyDict_SetItemString(aarch64ExtendDict, "SXTH",    PyLong_FromUint32(triton::arch::aarch64::ID_EXTEND_SXTH));
        xPyDict_SetItemString(aarch64ExtendDict, "SXTW",    PyLong_FromUint32(triton::arch::aarch64::ID_EXTEND_SXTW));
        xPyDict_SetItemString(aarch64ExtendDict, "SXTX",    PyLong_FromUint32(triton::arch::aarch64::ID_EXTEND_SXTX));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
