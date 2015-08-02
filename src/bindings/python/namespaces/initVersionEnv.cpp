/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <Version.h>


void initVersionEnv(PyObject *idVersionClassDict) {
  PyDict_SetItemString(idVersionClassDict, "MAJOR", PyInt_FromLong(TritonVersion::MAJOR));
  PyDict_SetItemString(idVersionClassDict, "MINOR", PyInt_FromLong(TritonVersion::MINOR));
  PyDict_SetItemString(idVersionClassDict, "BUILD", PyInt_FromLong(TritonVersion::BUILD));
}

