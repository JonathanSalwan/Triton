/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <CpuSize.h>


void initCpuSizeEnv(PyObject *idCpuSizeClassDict) {
  PyDict_SetItemString(idCpuSizeClassDict, "BYTE",        PyLong_FromLongLong(BYTE_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "BYTE_BIT",    PyLong_FromLongLong(BYTE_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "WORD",        PyLong_FromLongLong(WORD_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "WORD_BIT",    PyLong_FromLongLong(WORD_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "DWORD",       PyLong_FromLongLong(DWORD_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "DWORD_BIT",   PyLong_FromLongLong(DWORD_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "QWORD",       PyLong_FromLongLong(QWORD_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "QWORD_BIT",   PyLong_FromLongLong(QWORD_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "DQWORD",      PyLong_FromLongLong(DQWORD_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "DQWORD_BIT",  PyLong_FromLongLong(DQWORD_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "REG",         PyLong_FromLongLong(REG_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "REG_BIT",     PyLong_FromLongLong(REG_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "SSE_REG",     PyLong_FromLongLong(SSE_REG_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "SSE_REG_BIT", PyLong_FromLongLong(SSE_REG_SIZE_BIT));
}

