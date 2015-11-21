/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <IRBuilderOperand.h>


void initOperandEnv(PyObject *idOperandClassDict) {
  PyDict_SetItemString(idOperandClassDict, "IMM",   PyLong_FromUint(IRBuilderOperand::IMM));
  PyDict_SetItemString(idOperandClassDict, "LEA",   PyLong_FromUint(IRBuilderOperand::LEA));
  PyDict_SetItemString(idOperandClassDict, "MEM_R", PyLong_FromUint(IRBuilderOperand::MEM_R));
  PyDict_SetItemString(idOperandClassDict, "MEM_W", PyLong_FromUint(IRBuilderOperand::MEM_W));
  PyDict_SetItemString(idOperandClassDict, "REG",   PyLong_FromUint(IRBuilderOperand::REG));
}

