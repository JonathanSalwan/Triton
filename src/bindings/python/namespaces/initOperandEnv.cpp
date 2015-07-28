/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <IRBuilderOperand.h>


void initOperandEnv(PyObject *idOperandClassDict)
{
  PyDict_SetItemString(idOperandClassDict, "IMM",   PyInt_FromLong(IRBuilderOperand::IMM));
  PyDict_SetItemString(idOperandClassDict, "LEA",   PyInt_FromLong(IRBuilderOperand::LEA));
  PyDict_SetItemString(idOperandClassDict, "MEM_R", PyInt_FromLong(IRBuilderOperand::MEM_R));
  PyDict_SetItemString(idOperandClassDict, "MEM_W", PyInt_FromLong(IRBuilderOperand::MEM_W));
  PyDict_SetItemString(idOperandClassDict, "REG",   PyInt_FromLong(IRBuilderOperand::REG));
}

