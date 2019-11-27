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
    \brief [**python api**] All information about the SHIFT Python namespace.

\tableofcontents

\section SHIFT_py_description Description
<hr>

The SHIFT namespace contains all kinds of shift operands for AArch64.

\section SHIFT_py_api Python API - Items of the SHIFT namespace
<hr>

- **SHIFT.ARM.INVALID**<br>
Invalid shift operand.

- **SHIFT.ARM.ASR**<br>
Arithmetic Shift Right operand.

- **SHIFT.ARM.LSL**<br>
Logical Shift Left operand.

- **SHIFT.ARM.LSR**<br>
Logical Shift Right operand.

- **SHIFT.ARM.ROR**<br>
Rotate Right operand.

- **SHIFT.ARM.RRX**<br>
Rotate Right with Extend operand.

- **SHIFT.ARM.ASR_REG**<br>
Arithmetic Shift Right operand.

- **SHIFT.ARM.LSL_REG**<br>
Logical Shift Left operand.

- **SHIFT.ARM.LSR_REG**<br>
Logical Shift Right operand.

- **SHIFT.ARM.ROR_REG**<br>
Rotate Right operand.

- **SHIFT.ARM.RRX_REG**<br>
Rotate Right with Extend operand.

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initShiftsNamespace(PyObject* shiftsDict) {
        PyDict_Clear(shiftsDict);

        PyObject* armShiftsDict = xPyDict_New();

        xPyDict_SetItemString(armShiftsDict, "INVALID", PyLong_FromUint32(triton::arch::arm::ID_SHIFT_INVALID));
        xPyDict_SetItemString(armShiftsDict, "ASR",     PyLong_FromUint32(triton::arch::arm::ID_SHIFT_ASR));
        xPyDict_SetItemString(armShiftsDict, "LSL",     PyLong_FromUint32(triton::arch::arm::ID_SHIFT_LSL));
        xPyDict_SetItemString(armShiftsDict, "LSR",     PyLong_FromUint32(triton::arch::arm::ID_SHIFT_LSR));
        xPyDict_SetItemString(armShiftsDict, "ROR",     PyLong_FromUint32(triton::arch::arm::ID_SHIFT_ROR));
        xPyDict_SetItemString(armShiftsDict, "RRX",     PyLong_FromUint32(triton::arch::arm::ID_SHIFT_RRX));
        xPyDict_SetItemString(armShiftsDict, "ASR_REG", PyLong_FromUint32(triton::arch::arm::ID_SHIFT_ASR_REG));
        xPyDict_SetItemString(armShiftsDict, "LSL_REG", PyLong_FromUint32(triton::arch::arm::ID_SHIFT_LSL_REG));
        xPyDict_SetItemString(armShiftsDict, "LSR_REG", PyLong_FromUint32(triton::arch::arm::ID_SHIFT_LSR_REG));
        xPyDict_SetItemString(armShiftsDict, "ROR_REG", PyLong_FromUint32(triton::arch::arm::ID_SHIFT_ROR_REG));
        xPyDict_SetItemString(armShiftsDict, "RRX_REG", PyLong_FromUint32(triton::arch::arm::ID_SHIFT_RRX_REG));

        PyObject* armShiftsDictClass = xPyClass_New(nullptr, armShiftsDict, xPyString_FromString("ARM"));
        xPyDict_SetItemString(shiftsDict, "ARM", armShiftsDictClass);
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
