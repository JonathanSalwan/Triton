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



/*! \page py_SYMEXPR_page SYMEXPR
    \brief [**python api**] All information about the SYMEXPR python namespace.

\tableofcontents

\section SYMEXPR_py_description Description
<hr>

The SYMEXPR namespace contains all kinds and states of a symbolic expression.

\section SYMEXPR_py_api Python API - Items of the SYMEXPR namespace
<hr>

- **SYMEXPR.UNDEF**
- **SYMEXPR.MEM**
- **SYMEXPR.REG**

*/



namespace triton {
  namespace bindings {
    namespace python {

#ifdef IS_PY3
      NAMESPACE_TYPE(SYMEXPR, SymExprNamespace)

      PyObject* initSymExprNamespace() {
        PyType_Ready(&SymExprNamespace_Type);
        PyObject* symExprDict = SymExprNamespace_Type.tp_dict;
#else
      void initSymExprNamespace(PyObject* symExprDict) {
#endif
        xPyDict_SetItemString(symExprDict, "UNDEF",  PyLong_FromUint32(triton::engines::symbolic::UNDEF));
        xPyDict_SetItemString(symExprDict, "MEM",    PyLong_FromUint32(triton::engines::symbolic::MEM));
        xPyDict_SetItemString(symExprDict, "REG",    PyLong_FromUint32(triton::engines::symbolic::REG));
#ifdef IS_PY3
        return _PyObject_New(&SymExprNamespace_Type);
#endif
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
