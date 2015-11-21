/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <SymbolicExpression.h>


void initSymExprEnv(PyObject *idSymExprClassDict) {
  PyDict_SetItemString(idSymExprClassDict, "MEM", PyLong_FromUint(SymExpr::MEM));
  PyDict_SetItemString(idSymExprClassDict, "REG", PyLong_FromUint(SymExpr::REG));
  PyDict_SetItemString(idSymExprClassDict, "UNDEF", PyLong_FromUint(SymExpr::UNDEF));
}

#endif

