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
  PyDict_SetItemString(idCallbackClassDict, "AFTER", PyLong_FromUint(CB_AFTER));
  PyDict_SetItemString(idCallbackClassDict, "BEFORE", PyLong_FromUint(CB_BEFORE));
  PyDict_SetItemString(idCallbackClassDict, "BEFORE_SYMPROC", PyLong_FromUint(CB_BEFORE_SYMPROC));
  PyDict_SetItemString(idCallbackClassDict, "FINI", PyLong_FromUint(CB_FINI));
  PyDict_SetItemString(idCallbackClassDict, "ROUTINE_ENTRY", PyLong_FromUint(CB_ROUTINE_ENTRY));
  PyDict_SetItemString(idCallbackClassDict, "ROUTINE_EXIT", PyLong_FromUint(CB_ROUTINE_EXIT));
  PyDict_SetItemString(idCallbackClassDict, "SIGNALS", PyLong_FromUint(CB_SIGNALS));
  PyDict_SetItemString(idCallbackClassDict, "SYSCALL_ENTRY", PyLong_FromUint(CB_SYSCALL_ENTRY));
  PyDict_SetItemString(idCallbackClassDict, "SYSCALL_EXIT", PyLong_FromUint(CB_SYSCALL_EXIT));
  PyDict_SetItemString(idCallbackClassDict, "IMAGE_LOAD", PyLong_FromUint(CB_IMAGE_LOAD));
}

