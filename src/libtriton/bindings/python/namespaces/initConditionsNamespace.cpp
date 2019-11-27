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
    \brief [**python api**] All information about the CONDITION Python namespace.

\tableofcontents

\section CONDITION_py_description Description
<hr>

The CONDITION namespace contains all kinds of instruction conditions for AArch64.

\section CONDITION_py_api Python API - Items of the CONDITION namespace
<hr>

- **CONDITION.ARM.INVALID**<br>
Invalid code condition.

- **CONDITION.ARM.AL**<br>
Always. Any flags. This suffix is normally omitted.

- **CONDITION.ARM.EQ**<br>
Equal. Z set.

- **CONDITION.ARM.GE**<br>
Signed >=. N and V the same.

- **CONDITION.ARM.GT**<br>
Signed >. Z clear, N and V the same.

- **CONDITION.ARM.HI**<br>
Higher (unsigned >). C set and Z clear.

- **CONDITION.ARM.HS**<br>
Higher or same (unsigned >=). C set.

- **CONDITION.ARM.LE**<br>
Signed <=. Z set, N and V differ.

- **CONDITION.ARM.LO**<br>
Lower (unsigned <). C clear.

- **CONDITION.ARM.LS**<br>
Lower or same (unsigned <=). C clear or Z set.

- **CONDITION.ARM.LT**<br>
Signed <. N and V differ.

- **CONDITION.ARM.MI**<br>
Negative. N set.

- **CONDITION.ARM.NE**<br>
Not equal. Z clear.

- **CONDITION.ARM.PL**<br>
Positive or zero. N clear.

- **CONDITION.ARM.VC**<br>
No overflow. V clear.

- **CONDITION.ARM.VS**<br>
Overflow. V set.

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initConditionsNamespace(PyObject* conditionsDict) {
        PyDict_Clear(conditionsDict);

        PyObject* armConditionsDict = xPyDict_New();

        xPyDict_SetItemString(armConditionsDict, "INVALID", PyLong_FromUint32(triton::arch::arm::ID_CONDITION_INVALID));
        xPyDict_SetItemString(armConditionsDict, "AL",      PyLong_FromUint32(triton::arch::arm::ID_CONDITION_AL));
        xPyDict_SetItemString(armConditionsDict, "EQ",      PyLong_FromUint32(triton::arch::arm::ID_CONDITION_EQ));
        xPyDict_SetItemString(armConditionsDict, "GE",      PyLong_FromUint32(triton::arch::arm::ID_CONDITION_GE));
        xPyDict_SetItemString(armConditionsDict, "GT",      PyLong_FromUint32(triton::arch::arm::ID_CONDITION_GT));
        xPyDict_SetItemString(armConditionsDict, "HI",      PyLong_FromUint32(triton::arch::arm::ID_CONDITION_HI));
        xPyDict_SetItemString(armConditionsDict, "HS",      PyLong_FromUint32(triton::arch::arm::ID_CONDITION_HS));
        xPyDict_SetItemString(armConditionsDict, "LE",      PyLong_FromUint32(triton::arch::arm::ID_CONDITION_LE));
        xPyDict_SetItemString(armConditionsDict, "LO",      PyLong_FromUint32(triton::arch::arm::ID_CONDITION_LO));
        xPyDict_SetItemString(armConditionsDict, "LS",      PyLong_FromUint32(triton::arch::arm::ID_CONDITION_LS));
        xPyDict_SetItemString(armConditionsDict, "LT",      PyLong_FromUint32(triton::arch::arm::ID_CONDITION_LT));
        xPyDict_SetItemString(armConditionsDict, "MI",      PyLong_FromUint32(triton::arch::arm::ID_CONDITION_MI));
        xPyDict_SetItemString(armConditionsDict, "NE",      PyLong_FromUint32(triton::arch::arm::ID_CONDITION_NE));
        xPyDict_SetItemString(armConditionsDict, "PL",      PyLong_FromUint32(triton::arch::arm::ID_CONDITION_PL));
        xPyDict_SetItemString(armConditionsDict, "VC",      PyLong_FromUint32(triton::arch::arm::ID_CONDITION_VC));
        xPyDict_SetItemString(armConditionsDict, "VS",      PyLong_FromUint32(triton::arch::arm::ID_CONDITION_VS));

        PyObject* armConditionsDictClass = xPyClass_New(nullptr, armConditionsDict, xPyString_FromString("ARM"));
        xPyDict_SetItemString(conditionsDict, "ARM", armConditionsDictClass);
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
