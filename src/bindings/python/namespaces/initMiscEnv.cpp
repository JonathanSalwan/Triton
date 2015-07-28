/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <Misc.h>


void initMiscEnv(PyObject *idMiscClassDict)
{
  PyDict_SetItemString(idMiscClassDict, "UNSET", Py_BuildValue("k", UNSET));
}

