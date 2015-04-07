
#include <iostream>
#include <python2.7/Python.h>

#include "PythonBindings.h"
#include "xPyFunc.h"

void initRegEnv(PyObject *);
void initFlagEnv(PyObject *);

/*
 * Triton: [IDREF, callback, CB_AFTER, CB_BEFORE]
 * IDREF: [REG, FLAG]
 * REG: [RAX, RBX, XMM0, ...]
 * FLAG: [AF, OF, ZF, ...]
 */

PyObject *initBindings(void)
{
  Py_Initialize();

  PyObject *tritonModule = Py_InitModule("triton", pythonCallbacks);

  if (tritonModule == NULL) {
    std::cerr << "Failed to initialize Triton bindings" << std::endl;
    PyErr_Print();
    exit(1);
  }

  /* Create the IDREF class */
  PyObject *idRefClassName = xPyString_FromString("IDREF");
  PyObject *idRefClassDict = xPyDict_New();

  /* Create the IDREF.REG class */
  PyObject *idRegClassName = xPyString_FromString("REG");
  PyObject *idRegClassDict = xPyDict_New();

  /* Add registers ref into IDREF.REG class */
  initRegEnv(idRegClassDict);

  /* Create the REG class */
  PyObject *idRegClass = xPyClass_New(NULL, idRegClassDict, idRegClassName);

  /* Create the IDREF.FLAG class */
  PyObject *idFlagClassName = xPyString_FromString("FLAG");
  PyObject *idFlagClassDict = xPyDict_New();

  /* Add flags ref into IDREF.FLAG class */
  initFlagEnv(idFlagClassDict);

  /* Create the FLAG class */
  PyObject *idFlagClass = xPyClass_New(NULL, idFlagClassDict, idFlagClassName);

  /* Add REG and FLAG into IDREF */
  PyDict_SetItemString(idRefClassDict, "REG", idRegClass);
  PyDict_SetItemString(idRefClassDict, "FLAG", idFlagClass);

  /* Create the IDREF class */
  PyObject *idRefClass = xPyClass_New(NULL, idRefClassDict, idRefClassName);

  /* add IDREF into triton module */
  PyModule_AddObject(tritonModule, "IDREF", idRefClass);

  /* Constants Triton internal */
  PyModule_AddIntConstant(tritonModule, "CB_BEFORE",  CB_BEFORE);
  PyModule_AddIntConstant(tritonModule, "CB_AFTER",   CB_AFTER);

  return tritonModule;
}


bool execBindings(const char *fileName)
{
  FILE *fd = fopen(fileName, "r");
  if (fd == NULL) {
    perror("fopen");
    return false;
  }
  PyRun_SimpleFile(fd, fileName);
  fclose(fd);
  return true;
}

