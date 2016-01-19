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
#include <symbolicExpression.hpp>

#ifdef __unix__
  #include <python2.7/Python.h>
#elif _WIN32
  #include <Python.h>
#endif



/*! \page py_SYMEXPR_page SYMEXPR
    \brief [**python api**] All information about the SYMEXPR python namespace.

\tableofcontents

\section SYMEXPR_py_description Description
<hr>

The SYMEXPR namespace contains all kinds and states of a symbolic expression.

\section SYMEXPR_py_api Python API - Items of the SYMEXPR namespace
<hr>

- **SYMEXPR.UNSET**
- **SYMEXPR.UNDEF**
- **SYMEXPR.MEM**
- **SYMEXPR.REG**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initSymExprNamespace(PyObject* symExprDict) {

        PyDict_SetItemString(symExprDict, "UNSET", PyLong_FromUint(static_cast<triton::__uint>(-1)));
        PyDict_SetItemString(symExprDict, "UNDEF", PyLong_FromUint(triton::engines::symbolic::UNDEF));
        PyDict_SetItemString(symExprDict, "MEM", PyLong_FromUint(triton::engines::symbolic::MEM));
        PyDict_SetItemString(symExprDict, "REG", PyLong_FromUint(triton::engines::symbolic::REG));

      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
