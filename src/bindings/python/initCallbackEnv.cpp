
#include <python2.7/Python.h>

#include "CallbackDefine.h"
#include "IRBuilderOperand.h"
#include "PythonBindings.h"


void initCallbackEnv(PyObject *idCallbackClassDict)
{
  PyDict_SetItemString(idCallbackClassDict, "AFTER",   PyInt_FromLong(CB_AFTER));
  PyDict_SetItemString(idCallbackClassDict, "BEFORE",  PyInt_FromLong(CB_BEFORE));
  PyDict_SetItemString(idCallbackClassDict, "FINI",    PyInt_FromLong(CB_FINI));
}

