/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <Registers.h>


void initRegEnv(PyObject *idRegClassDict)
{
  PyDict_SetItemString(idRegClassDict, "INVALID", PyInt_FromLong(ID_INVALID));
  PyDict_SetItemString(idRegClassDict, "RAX", PyInt_FromLong(ID_RAX));
  PyDict_SetItemString(idRegClassDict, "RBX", PyInt_FromLong(ID_RBX));
  PyDict_SetItemString(idRegClassDict, "RCX", PyInt_FromLong(ID_RCX));
  PyDict_SetItemString(idRegClassDict, "RDX", PyInt_FromLong(ID_RDX));
  PyDict_SetItemString(idRegClassDict, "RDI", PyInt_FromLong(ID_RDI));
  PyDict_SetItemString(idRegClassDict, "RSI", PyInt_FromLong(ID_RSI));
  PyDict_SetItemString(idRegClassDict, "RBP", PyInt_FromLong(ID_RBP));
  PyDict_SetItemString(idRegClassDict, "RSP", PyInt_FromLong(ID_RSP));
  PyDict_SetItemString(idRegClassDict, "RIP", PyInt_FromLong(ID_RIP));
  PyDict_SetItemString(idRegClassDict, "RFLAGS", PyInt_FromLong(ID_RFLAGS));
  PyDict_SetItemString(idRegClassDict, "R8", PyInt_FromLong(ID_R8));
  PyDict_SetItemString(idRegClassDict, "R9", PyInt_FromLong(ID_R9));
  PyDict_SetItemString(idRegClassDict, "R10", PyInt_FromLong(ID_R10));
  PyDict_SetItemString(idRegClassDict, "R11", PyInt_FromLong(ID_R11));
  PyDict_SetItemString(idRegClassDict, "R12", PyInt_FromLong(ID_R12));
  PyDict_SetItemString(idRegClassDict, "R13", PyInt_FromLong(ID_R13));
  PyDict_SetItemString(idRegClassDict, "R14", PyInt_FromLong(ID_R14));
  PyDict_SetItemString(idRegClassDict, "R15", PyInt_FromLong(ID_R15));
  PyDict_SetItemString(idRegClassDict, "XMM0", PyInt_FromLong(ID_XMM0));
  PyDict_SetItemString(idRegClassDict, "XMM1", PyInt_FromLong(ID_XMM1));
  PyDict_SetItemString(idRegClassDict, "XMM2", PyInt_FromLong(ID_XMM2));
  PyDict_SetItemString(idRegClassDict, "XMM3", PyInt_FromLong(ID_XMM3));
  PyDict_SetItemString(idRegClassDict, "XMM4", PyInt_FromLong(ID_XMM4));
  PyDict_SetItemString(idRegClassDict, "XMM5", PyInt_FromLong(ID_XMM5));
  PyDict_SetItemString(idRegClassDict, "XMM6", PyInt_FromLong(ID_XMM6));
  PyDict_SetItemString(idRegClassDict, "XMM7", PyInt_FromLong(ID_XMM7));
  PyDict_SetItemString(idRegClassDict, "XMM8", PyInt_FromLong(ID_XMM8));
  PyDict_SetItemString(idRegClassDict, "XMM9", PyInt_FromLong(ID_XMM9));
  PyDict_SetItemString(idRegClassDict, "XMM10", PyInt_FromLong(ID_XMM10));
  PyDict_SetItemString(idRegClassDict, "XMM11", PyInt_FromLong(ID_XMM11));
  PyDict_SetItemString(idRegClassDict, "XMM12", PyInt_FromLong(ID_XMM12));
  PyDict_SetItemString(idRegClassDict, "XMM13", PyInt_FromLong(ID_XMM13));
  PyDict_SetItemString(idRegClassDict, "XMM14", PyInt_FromLong(ID_XMM14));
  PyDict_SetItemString(idRegClassDict, "XMM15", PyInt_FromLong(ID_XMM15));
}

