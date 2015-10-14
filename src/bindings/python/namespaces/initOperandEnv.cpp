/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <IRBuilderOperand.h>


void initOperandEnv(PyObject *idOperandClassDict) {
  PyDict_SetItemString(idOperandClassDict, "IMM",   PyLong_FromLongLong(IRBuilderOperand::IMM));
  PyDict_SetItemString(idOperandClassDict, "LEA",   PyLong_FromLongLong(IRBuilderOperand::LEA));
  PyDict_SetItemString(idOperandClassDict, "MEM_R", PyLong_FromLongLong(IRBuilderOperand::MEM_R));
  PyDict_SetItemString(idOperandClassDict, "MEM_W", PyLong_FromLongLong(IRBuilderOperand::MEM_W));
  PyDict_SetItemString(idOperandClassDict, "REG",   PyLong_FromLongLong(IRBuilderOperand::REG));
}

