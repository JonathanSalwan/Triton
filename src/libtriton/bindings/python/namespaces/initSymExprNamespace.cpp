//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/symbolicExpression.hpp>



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
        PyDict_SetItemString(symExprDict, "UNSET",  PyLong_FromUsize(static_cast<triton::usize>(-1)));
        PyDict_SetItemString(symExprDict, "UNDEF",  PyLong_FromUint32(triton::engines::symbolic::UNDEF));
        PyDict_SetItemString(symExprDict, "MEM",    PyLong_FromUint32(triton::engines::symbolic::MEM));
        PyDict_SetItemString(symExprDict, "REG",    PyLong_FromUint32(triton::engines::symbolic::REG));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
