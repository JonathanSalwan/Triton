
#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <SymbolicVariable.h>


void initSymVarEnv(PyObject *idSymVarClassDict)
{
  PyDict_SetItemString(idSymVarClassDict, "MEM", PyInt_FromLong(SymVar::MEM));
  PyDict_SetItemString(idSymVarClassDict, "REG", PyInt_FromLong(SymVar::REG));
  PyDict_SetItemString(idSymVarClassDict, "UNDEF", PyInt_FromLong(SymVar::UNDEF));
}

