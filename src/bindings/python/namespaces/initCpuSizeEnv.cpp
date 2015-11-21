/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <CpuSize.h>


void initCpuSizeEnv(PyObject *idCpuSizeClassDict) {
  PyDict_SetItemString(idCpuSizeClassDict, "BYTE",        PyLong_FromUint(BYTE_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "BYTE_BIT",    PyLong_FromUint(BYTE_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "WORD",        PyLong_FromUint(WORD_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "WORD_BIT",    PyLong_FromUint(WORD_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "DWORD",       PyLong_FromUint(DWORD_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "DWORD_BIT",   PyLong_FromUint(DWORD_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "QWORD",       PyLong_FromUint(QWORD_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "QWORD_BIT",   PyLong_FromUint(QWORD_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "DQWORD",      PyLong_FromUint(DQWORD_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "DQWORD_BIT",  PyLong_FromUint(DQWORD_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "REG",         PyLong_FromUint(REG_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "REG_BIT",     PyLong_FromUint(REG_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "SSE_REG",     PyLong_FromUint(SSE_REG_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "SSE_REG_BIT", PyLong_FromUint(SSE_REG_SIZE_BIT));
}

