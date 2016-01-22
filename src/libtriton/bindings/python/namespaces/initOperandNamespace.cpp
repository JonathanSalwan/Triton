//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <operandInterface.hpp>
#include <pythonBindings.hpp>
#include <pythonUtils.hpp>

#ifdef __unix__
  #include <python2.7/Python.h>
#elif _WIN32
  #include <Python.h>
#endif



/*! \page py_OPERAND_page OPERAND
    \brief [**python api**] All information about the OPERAND python namespace.

\tableofcontents

\section OPERAND_py_description Description
<hr>

The OPERAND namespace contains all kinds of operand.

\section OPERAND_py_api Python API - Items of the OPERAND namespace
<hr>

- **OPERAND.INVALID**
- **OPERAND.IMM**
- **OPERAND.MEM**
- **OPERAND.REG**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initOperandNamespace(PyObject* operandDict) {

        PyDict_SetItemString(operandDict, "INVALID", PyLong_FromUint(triton::arch::OP_INVALID));
        PyDict_SetItemString(operandDict, "IMM", PyLong_FromUint(triton::arch::OP_IMM));
        PyDict_SetItemString(operandDict, "MEM", PyLong_FromUint(triton::arch::OP_MEM));
        PyDict_SetItemString(operandDict, "REG", PyLong_FromUint(triton::arch::OP_REG));

      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
