/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <python2.7/Python.h>

#include <CallbackDefine.h>
#include <IRBuilderOperand.h>
#include <PythonBindings.h>


void initCallbackEnv(PyObject *idCallbackClassDict) {
  PyDict_SetItemString(idCallbackClassDict, "AFTER", PyLong_FromLongLong(CB_AFTER));
  PyDict_SetItemString(idCallbackClassDict, "BEFORE", PyLong_FromLongLong(CB_BEFORE));
  PyDict_SetItemString(idCallbackClassDict, "BEFORE_SYMPROC", PyLong_FromLongLong(CB_BEFORE_SYMPROC));
  PyDict_SetItemString(idCallbackClassDict, "FINI", PyLong_FromLongLong(CB_FINI));
  PyDict_SetItemString(idCallbackClassDict, "ROUTINE_ENTRY", PyLong_FromLongLong(CB_ROUTINE_ENTRY));
  PyDict_SetItemString(idCallbackClassDict, "ROUTINE_EXIT", PyLong_FromLongLong(CB_ROUTINE_EXIT));
  PyDict_SetItemString(idCallbackClassDict, "SIGNALS", PyLong_FromLongLong(CB_SIGNALS));
  PyDict_SetItemString(idCallbackClassDict, "SYSCALL_ENTRY", PyLong_FromLongLong(CB_SYSCALL_ENTRY));
  PyDict_SetItemString(idCallbackClassDict, "SYSCALL_EXIT", PyLong_FromLongLong(CB_SYSCALL_EXIT));
  PyDict_SetItemString(idCallbackClassDict, "IMAGE_LOAD", PyLong_FromLongLong(CB_IMAGE_LOAD));
}

