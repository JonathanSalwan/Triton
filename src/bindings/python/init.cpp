
#include <iostream>
#include <python2.7/Python.h>

#include "PythonBindings.h"
#include "Registers.h"
#include "xPyFunc.h"


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
  PyDict_SetItemString(idRegClassDict, "RAX", PyInt_FromLong(ID_RAX));
  PyDict_SetItemString(idRegClassDict, "RBX", PyInt_FromLong(ID_RBX));
  PyDict_SetItemString(idRegClassDict, "RCX", PyInt_FromLong(ID_RCX));
  PyDict_SetItemString(idRegClassDict, "RDX", PyInt_FromLong(ID_RDX));
  PyDict_SetItemString(idRegClassDict, "RDI", PyInt_FromLong(ID_RDI));
  PyDict_SetItemString(idRegClassDict, "RSI", PyInt_FromLong(ID_RSI));
  PyDict_SetItemString(idRegClassDict, "RBP", PyInt_FromLong(ID_RBP));
  PyDict_SetItemString(idRegClassDict, "RSP", PyInt_FromLong(ID_RSP));
  PyDict_SetItemString(idRegClassDict, "RIP", PyInt_FromLong(ID_RIP));
  PyDict_SetItemString(idRegClassDict, "R8", PyInt_FromLong(ID_R8));
  PyDict_SetItemString(idRegClassDict, "R9", PyInt_FromLong(ID_R9));
  PyDict_SetItemString(idRegClassDict, "R10", PyInt_FromLong(ID_R10));
  PyDict_SetItemString(idRegClassDict, "R11", PyInt_FromLong(ID_R11));
  PyDict_SetItemString(idRegClassDict, "R12", PyInt_FromLong(ID_R12));
  PyDict_SetItemString(idRegClassDict, "R13", PyInt_FromLong(ID_R13));
  PyDict_SetItemString(idRegClassDict, "R14", PyInt_FromLong(ID_R14));
  PyDict_SetItemString(idRegClassDict, "R15", PyInt_FromLong(ID_R15));
  PyDict_SetItemString(idRegClassDict, "XMM0", PyInt_FromLong(ID_XMM0));
  PyDict_SetItemString(idRegClassDict, "XMM1", PyInt_FromLong(ID_XMM1));
  PyDict_SetItemString(idRegClassDict, "XMM2", PyInt_FromLong(ID_XMM2));
  PyDict_SetItemString(idRegClassDict, "XMM3", PyInt_FromLong(ID_XMM3));
  PyDict_SetItemString(idRegClassDict, "XMM4", PyInt_FromLong(ID_XMM4));
  PyDict_SetItemString(idRegClassDict, "XMM5", PyInt_FromLong(ID_XMM5));
  PyDict_SetItemString(idRegClassDict, "XMM6", PyInt_FromLong(ID_XMM6));
  PyDict_SetItemString(idRegClassDict, "XMM7", PyInt_FromLong(ID_XMM7));
  PyDict_SetItemString(idRegClassDict, "XMM8", PyInt_FromLong(ID_XMM8));
  PyDict_SetItemString(idRegClassDict, "XMM9", PyInt_FromLong(ID_XMM9));
  PyDict_SetItemString(idRegClassDict, "XMM10", PyInt_FromLong(ID_XMM10));
  PyDict_SetItemString(idRegClassDict, "XMM11", PyInt_FromLong(ID_XMM11));
  PyDict_SetItemString(idRegClassDict, "XMM12", PyInt_FromLong(ID_XMM12));
  PyDict_SetItemString(idRegClassDict, "XMM13", PyInt_FromLong(ID_XMM13));
  PyDict_SetItemString(idRegClassDict, "XMM14", PyInt_FromLong(ID_XMM14));
  PyDict_SetItemString(idRegClassDict, "XMM15", PyInt_FromLong(ID_XMM15));

  /* Create the REG class */
  PyObject *idRegClass = xPyClass_New(NULL, idRegClassDict, idRegClassName);

  /* Create the IDREF.FLAG class */
  PyObject *idFlagClassName = xPyString_FromString("FLAG");
  PyObject *idFlagClassDict = xPyDict_New();

  PyDict_SetItemString(idFlagClassDict, "AF", PyInt_FromLong(ID_AF));
  PyDict_SetItemString(idFlagClassDict, "CF", PyInt_FromLong(ID_CF));
  PyDict_SetItemString(idFlagClassDict, "DF", PyInt_FromLong(ID_DF));
  PyDict_SetItemString(idFlagClassDict, "IF", PyInt_FromLong(ID_IF));
  PyDict_SetItemString(idFlagClassDict, "OF", PyInt_FromLong(ID_OF));
  PyDict_SetItemString(idFlagClassDict, "PF", PyInt_FromLong(ID_PF));
  PyDict_SetItemString(idFlagClassDict, "SF", PyInt_FromLong(ID_SF));
  PyDict_SetItemString(idFlagClassDict, "TF", PyInt_FromLong(ID_TF));
  PyDict_SetItemString(idFlagClassDict, "ZF", PyInt_FromLong(ID_ZF));

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

