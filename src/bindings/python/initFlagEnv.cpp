
#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <Registers.h>


void initFlagEnv(PyObject *idFlagClassDict)
{
  PyDict_SetItemString(idFlagClassDict, "AF", PyInt_FromLong(ID_AF));
  PyDict_SetItemString(idFlagClassDict, "CF", PyInt_FromLong(ID_CF));
  PyDict_SetItemString(idFlagClassDict, "DF", PyInt_FromLong(ID_DF));
  PyDict_SetItemString(idFlagClassDict, "IF", PyInt_FromLong(ID_IF));
  PyDict_SetItemString(idFlagClassDict, "OF", PyInt_FromLong(ID_OF));
  PyDict_SetItemString(idFlagClassDict, "PF", PyInt_FromLong(ID_PF));
  PyDict_SetItemString(idFlagClassDict, "SF", PyInt_FromLong(ID_SF));
  PyDict_SetItemString(idFlagClassDict, "TF", PyInt_FromLong(ID_TF));
  PyDict_SetItemString(idFlagClassDict, "ZF", PyInt_FromLong(ID_ZF));
}

