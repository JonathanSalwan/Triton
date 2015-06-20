
#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <CpuSize.h>


void initCpuSizeEnv(PyObject *idCpuSizeClassDict)
{
  PyDict_SetItemString(idCpuSizeClassDict, "BYTE",        PyInt_FromLong(BYTE_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "BYTE_BIT",    PyInt_FromLong(BYTE_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "WORD",        PyInt_FromLong(WORD_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "WORD_BIT",    PyInt_FromLong(WORD_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "DWORD",       PyInt_FromLong(DWORD_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "DWORD_BIT",   PyInt_FromLong(DWORD_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "QWORD",       PyInt_FromLong(QWORD_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "QWORD_BIT",   PyInt_FromLong(QWORD_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "DQWORD",      PyInt_FromLong(DQWORD_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "DQWORD_BIT",  PyInt_FromLong(DQWORD_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "REG",         PyInt_FromLong(REG_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "REG_BIT",     PyInt_FromLong(REG_SIZE_BIT));
  PyDict_SetItemString(idCpuSizeClassDict, "SSE_REG",     PyInt_FromLong(SSE_REG_SIZE));
  PyDict_SetItemString(idCpuSizeClassDict, "SSE_REG_BIT", PyInt_FromLong(SSE_REG_SIZE_BIT));
}

