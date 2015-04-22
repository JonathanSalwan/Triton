
#include <python2.7/Python.h>

#include "CallbackDefine.h"
#include "IRBuilderOperand.h"
#include "PythonBindings.h"


void initCallbackEnv(PyObject *idCallbackClassDict)
{
  PyDict_SetItemString(idCallbackClassDict, "AFTER", PyInt_FromLong(CB_AFTER));
  PyDict_SetItemString(idCallbackClassDict, "BEFORE", PyInt_FromLong(CB_BEFORE));
  PyDict_SetItemString(idCallbackClassDict, "BEFORE_IRPROC", PyInt_FromLong(CB_BEFORE_IRPROC));
  PyDict_SetItemString(idCallbackClassDict, "FINI", PyInt_FromLong(CB_FINI));
  PyDict_SetItemString(idCallbackClassDict, "SYSCALL_ENTRY", PyInt_FromLong(CB_SYSCALL_ENTRY));
  PyDict_SetItemString(idCallbackClassDict, "SYSCALL_EXIT", PyInt_FromLong(CB_SYSCALL_EXIT));
}

