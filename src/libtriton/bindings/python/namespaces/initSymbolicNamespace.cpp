//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/symbolicExpression.hpp>



/*! \page py_SYMBOLIC_page SYMBOLIC
    \brief [**python api**] All information about the SYMBOLIC python namespace.

\tableofcontents

\section SYMBOLIC_py_description Description
<hr>

The SYMBOLIC namespace contains all types of symbolic expressions and variables.

\section SYMBOLIC_py_api Python API - Items of the SYMBOLIC namespace
<hr>

- **SYMBOLIC.MEMORY_EXPRESSION**
- **SYMBOLIC.MEMORY_VARIABLE**
- **SYMBOLIC.REGISTER_EXPRESSION**
- **SYMBOLIC.REGISTER_VARIABLE**
- **SYMBOLIC.UNDEFINED_VARIABLE**
- **SYMBOLIC.VOLATILE_EXPRESSION**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initSymbolicNamespace(PyObject* symbolicDict) {
        xPyDict_SetItemString(symbolicDict, "MEMORY_EXPRESSION",     PyLong_FromUint32(triton::engines::symbolic::MEMORY_EXPRESSION));
        xPyDict_SetItemString(symbolicDict, "MEMORY_VARIABLE",       PyLong_FromUint32(triton::engines::symbolic::MEMORY_VARIABLE));
        xPyDict_SetItemString(symbolicDict, "REGISTER_EXPRESSION",   PyLong_FromUint32(triton::engines::symbolic::REGISTER_EXPRESSION));
        xPyDict_SetItemString(symbolicDict, "REGISTER_VARIABLE",     PyLong_FromUint32(triton::engines::symbolic::REGISTER_VARIABLE));
        xPyDict_SetItemString(symbolicDict, "UNDEFINED_VARIABLE",    PyLong_FromUint32(triton::engines::symbolic::UNDEFINED_VARIABLE));
        xPyDict_SetItemString(symbolicDict, "VOLATILE_EXPRESSION",   PyLong_FromUint32(triton::engines::symbolic::VOLATILE_EXPRESSION));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
