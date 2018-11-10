//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/aarch64Specifications.hpp>



/*! \page py_CONDITION_page CONDITION
    \brief [**python api**] All information about the CONDITION python namespace.

\tableofcontents

\section CONDITION_py_description Description
<hr>

The CONDITION namespace contains all kinds of instruction condition for AArch64.

\section CONDITION_py_api Python API - Items of the CONDITION namespace
<hr>

- **CONDITION.AARCH64.INVALID**<br>
Invalid code condition.

- **CONDITION.AARCH64.AL**<br>
Always. Any flags. This suffix is normally omitted.

- **CONDITION.AARCH64.EQ**<br>
Equal. Z set.

- **CONDITION.AARCH64.GE**<br>
Signed >=. N and V the same.

- **CONDITION.AARCH64.GT**<br>
Signed >. Z clear, N and V the same.

- **CONDITION.AARCH64.HI**<br>
Higher (unsigned >). C set and Z clear.

- **CONDITION.AARCH64.HS**<br>
Higher or same (unsigned >=). C set.

- **CONDITION.AARCH64.LE**<br>
Signed <=. Z set, N and V differ.

- **CONDITION.AARCH64.LO**<br>
Lower (unsigned <). C clear.

- **CONDITION.AARCH64.LS**<br>
Lower or same (unsigned <=). C clear or Z set.

- **CONDITION.AARCH64.LT**<br>
Signed <. N and V differ.

- **CONDITION.AARCH64.MI**<br>
Negative. N set.

- **CONDITION.AARCH64.NE**<br>
Not equal. Z clear.

- **CONDITION.AARCH64.PL**<br>
Positive or zero. N clear.

- **CONDITION.AARCH64.VC**<br>
No overflow. V clear.

- **CONDITION.AARCH64.VS**<br>
Overflow. V set.

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initConditionsNamespace(PyObject* conditionsDict) {
        PyDict_Clear(conditionsDict);

        PyObject* aarch64ConditionsDict      = xPyDict_New();
        PyObject* aarch64ConditionsDictClass = xPyClass_New(nullptr, aarch64ConditionsDict, xPyString_FromString("AARCH64"));
        xPyDict_SetItemString(conditionsDict, "AARCH64", aarch64ConditionsDictClass);

        xPyDict_SetItemString(aarch64ConditionsDict, "INVALID", PyLong_FromUint32(triton::arch::aarch64::ID_CONDITION_INVALID));
        xPyDict_SetItemString(aarch64ConditionsDict, "AL",      PyLong_FromUint32(triton::arch::aarch64::ID_CONDITION_AL));
        xPyDict_SetItemString(aarch64ConditionsDict, "EQ",      PyLong_FromUint32(triton::arch::aarch64::ID_CONDITION_EQ));
        xPyDict_SetItemString(aarch64ConditionsDict, "GE",      PyLong_FromUint32(triton::arch::aarch64::ID_CONDITION_GE));
        xPyDict_SetItemString(aarch64ConditionsDict, "GT",      PyLong_FromUint32(triton::arch::aarch64::ID_CONDITION_GT));
        xPyDict_SetItemString(aarch64ConditionsDict, "HI",      PyLong_FromUint32(triton::arch::aarch64::ID_CONDITION_HI));
        xPyDict_SetItemString(aarch64ConditionsDict, "HS",      PyLong_FromUint32(triton::arch::aarch64::ID_CONDITION_HS));
        xPyDict_SetItemString(aarch64ConditionsDict, "LE",      PyLong_FromUint32(triton::arch::aarch64::ID_CONDITION_LE));
        xPyDict_SetItemString(aarch64ConditionsDict, "LO",      PyLong_FromUint32(triton::arch::aarch64::ID_CONDITION_LO));
        xPyDict_SetItemString(aarch64ConditionsDict, "LS",      PyLong_FromUint32(triton::arch::aarch64::ID_CONDITION_LS));
        xPyDict_SetItemString(aarch64ConditionsDict, "LT",      PyLong_FromUint32(triton::arch::aarch64::ID_CONDITION_LT));
        xPyDict_SetItemString(aarch64ConditionsDict, "MI",      PyLong_FromUint32(triton::arch::aarch64::ID_CONDITION_MI));
        xPyDict_SetItemString(aarch64ConditionsDict, "NE",      PyLong_FromUint32(triton::arch::aarch64::ID_CONDITION_NE));
        xPyDict_SetItemString(aarch64ConditionsDict, "PL",      PyLong_FromUint32(triton::arch::aarch64::ID_CONDITION_PL));
        xPyDict_SetItemString(aarch64ConditionsDict, "VC",      PyLong_FromUint32(triton::arch::aarch64::ID_CONDITION_VC));
        xPyDict_SetItemString(aarch64ConditionsDict, "VS",      PyLong_FromUint32(triton::arch::aarch64::ID_CONDITION_VS));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
