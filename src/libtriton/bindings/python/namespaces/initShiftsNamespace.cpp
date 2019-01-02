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



/*! \page py_SHIFT_page SHIFT
    \brief [**python api**] All information about the SHIFT python namespace.

\tableofcontents

\section SHIFT_py_description Description
<hr>

The SHIFT namespace contains all kinds of shift operand for AArch64.

\section SHIFT_py_api Python API - Items of the SHIFT namespace
<hr>

- **SHIFT.AARCH64.INVALID**<br>
Invalid shift operand.

- **SHIFT.AARCH64.ASR**<br>
Arithmetic Shift Right operand.

- **SHIFT.AARCH64.LSL**<br>
Logical Shift Left operand.

- **SHIFT.AARCH64.LSR**<br>
Logical Shift Right operand.

- **SHIFT.AARCH64.ROR**<br>
Rotate Right operand.

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initShiftsNamespace(PyObject* shiftsDict) {
        PyDict_Clear(shiftsDict);

        PyObject* aarch64ShiftsDict      = xPyDict_New();
        PyObject* aarch64ShiftsDictClass = xPyClass_New(nullptr, aarch64ShiftsDict, xPyString_FromString("AARCH64"));
        xPyDict_SetItemString(shiftsDict, "AARCH64", aarch64ShiftsDictClass);

        xPyDict_SetItemString(aarch64ShiftsDict, "INVALID", PyLong_FromUint32(triton::arch::aarch64::ID_SHIFT_INVALID));
        xPyDict_SetItemString(aarch64ShiftsDict, "ASR",     PyLong_FromUint32(triton::arch::aarch64::ID_SHIFT_ASR));
        xPyDict_SetItemString(aarch64ShiftsDict, "LSL",     PyLong_FromUint32(triton::arch::aarch64::ID_SHIFT_LSL));
        xPyDict_SetItemString(aarch64ShiftsDict, "LSR",     PyLong_FromUint32(triton::arch::aarch64::ID_SHIFT_LSR));
        xPyDict_SetItemString(aarch64ShiftsDict, "ROR",     PyLong_FromUint32(triton::arch::aarch64::ID_SHIFT_ROR));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
