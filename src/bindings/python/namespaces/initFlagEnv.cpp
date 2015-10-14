/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <Registers.h>


void initFlagEnv(PyObject *idFlagClassDict) {
  PyDict_SetItemString(idFlagClassDict, "AF", PyLong_FromLongLong(ID_AF));
  PyDict_SetItemString(idFlagClassDict, "CF", PyLong_FromLongLong(ID_CF));
  PyDict_SetItemString(idFlagClassDict, "DF", PyLong_FromLongLong(ID_DF));
  PyDict_SetItemString(idFlagClassDict, "IF", PyLong_FromLongLong(ID_IF));
  PyDict_SetItemString(idFlagClassDict, "OF", PyLong_FromLongLong(ID_OF));
  PyDict_SetItemString(idFlagClassDict, "PF", PyLong_FromLongLong(ID_PF));
  PyDict_SetItemString(idFlagClassDict, "SF", PyLong_FromLongLong(ID_SF));
  PyDict_SetItemString(idFlagClassDict, "TF", PyLong_FromLongLong(ID_TF));
  PyDict_SetItemString(idFlagClassDict, "ZF", PyLong_FromLongLong(ID_ZF));
}

