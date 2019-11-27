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
    \brief [**python api**] All information about the EXTEND Python namespace.

\tableofcontents

\section EXTEND_py_description Description
<hr>

The EXTEND namespace contains all kinds of extend operands for AArch64.

\section EXTEND_py_api Python API - Items of the EXTEND namespace
<hr>

- **EXTEND.ARM.INVALID**<br>
Invalid extend operand

- **EXTEND.ARM.UXTB**<br>
Extracts a byte (8-bit) value from a register and zero extends it to the size of the register

- **EXTEND.ARM.UXTH**<br>
Extracts a halfword (16-bit) value from a register and zero extends it to the size of the register

- **EXTEND.ARM.UXTW**<br>
Extracts a word (32-bit) value from a register and zero extends it to the size of the register

- **EXTEND.ARM.UXTX**<br>
Use the whole 64-bit register

- **EXTEND.ARM.SXTB**<br>
Extracts a byte (8-bit) value from a register and sign extends it to the size of the register

- **EXTEND.ARM.SXTH**<br>
Extracts a halfword (16-bit) value from a register and sign extends it to the size of the register

- **EXTEND.ARM.SXTW**<br>
Extracts a word (32-bit) value from a register and sign extends it to the size of the register

- **EXTEND.ARM.SXTX**<br>
Use the whole 64-bit register

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initExtendNamespace(PyObject* extendDict) {
        PyDict_Clear(extendDict);

        PyObject* armExtendDict = xPyDict_New();

        xPyDict_SetItemString(armExtendDict, "INVALID", PyLong_FromUint32(triton::arch::arm::ID_EXTEND_INVALID));
        xPyDict_SetItemString(armExtendDict, "UXTB",    PyLong_FromUint32(triton::arch::arm::ID_EXTEND_UXTB));
        xPyDict_SetItemString(armExtendDict, "UXTH",    PyLong_FromUint32(triton::arch::arm::ID_EXTEND_UXTH));
        xPyDict_SetItemString(armExtendDict, "UXTW",    PyLong_FromUint32(triton::arch::arm::ID_EXTEND_UXTW));
        xPyDict_SetItemString(armExtendDict, "UXTX",    PyLong_FromUint32(triton::arch::arm::ID_EXTEND_UXTX));
        xPyDict_SetItemString(armExtendDict, "SXTB",    PyLong_FromUint32(triton::arch::arm::ID_EXTEND_SXTB));
        xPyDict_SetItemString(armExtendDict, "SXTH",    PyLong_FromUint32(triton::arch::arm::ID_EXTEND_SXTH));
        xPyDict_SetItemString(armExtendDict, "SXTW",    PyLong_FromUint32(triton::arch::arm::ID_EXTEND_SXTW));
        xPyDict_SetItemString(armExtendDict, "SXTX",    PyLong_FromUint32(triton::arch::arm::ID_EXTEND_SXTX));

        PyObject* armExtendDictClass = xPyClass_New(nullptr, armExtendDict, xPyString_FromString("ARM"));
        xPyDict_SetItemString(extendDict, "ARM", armExtendDictClass);
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
