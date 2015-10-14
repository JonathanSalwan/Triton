/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <SymbolicVariable.h>


void initSymVarEnv(PyObject *idSymVarClassDict) {
  PyDict_SetItemString(idSymVarClassDict, "MEM", PyLong_FromLongLong(SymVar::MEM));
  PyDict_SetItemString(idSymVarClassDict, "REG", PyLong_FromLongLong(SymVar::REG));
  PyDict_SetItemString(idSymVarClassDict, "UNDEF", PyLong_FromLongLong(SymVar::UNDEF));
}

#endif

