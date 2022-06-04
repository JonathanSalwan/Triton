//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/archEnums.hpp>



/*! \page py_EXCEPTION_page EXCEPTION
    \brief [**python api**] All information about the EXCEPTION Python namespace.

\tableofcontents

\section EXCEPTION_py_description Description
<hr>

The EXCEPTION namespace contains all kinds of exceptions.

\section EXCEPTION_py_api Python API - Items of the EXCEPTION namespace
<hr>

- **EXCEPTION.NO_FAULT**<br>
No fault, execution succeed.

- **EXCEPTION.FAULT_DE**<br>
Fault raised: Divide-by-zero.

- **EXCEPTION.FAULT_BP**<br>
Fault raised: Breakpoint.

- **EXCEPTION.FAULT_UD**<br>
Fault raised: Instruction not supported.

- **EXCEPTION.FAULT_GP**<br>
Fault raised: General Protection Fault.

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initExceptionNamespace(PyObject* exceptionDict) {
        xPyDict_SetItemString(exceptionDict, "NO_FAULT", PyLong_FromUint32(triton::arch::NO_FAULT));
        xPyDict_SetItemString(exceptionDict, "FAULT_DE", PyLong_FromUint32(triton::arch::FAULT_DE));
        xPyDict_SetItemString(exceptionDict, "FAULT_BP", PyLong_FromUint32(triton::arch::FAULT_BP));
        xPyDict_SetItemString(exceptionDict, "FAULT_UD", PyLong_FromUint32(triton::arch::FAULT_UD));
        xPyDict_SetItemString(exceptionDict, "FAULT_GP", PyLong_FromUint32(triton::arch::FAULT_GP));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
