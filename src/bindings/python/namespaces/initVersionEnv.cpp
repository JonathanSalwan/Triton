/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <Version.h>


void initVersionEnv(PyObject *idVersionClassDict) {
  PyDict_SetItemString(idVersionClassDict, "MAJOR", PyLong_FromUint(TritonVersion::MAJOR));
  PyDict_SetItemString(idVersionClassDict, "MINOR", PyLong_FromUint(TritonVersion::MINOR));
  PyDict_SetItemString(idVersionClassDict, "BUILD", PyLong_FromUint(TritonVersion::BUILD));
}

