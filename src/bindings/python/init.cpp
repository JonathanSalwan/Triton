
#include <python2.7/Python.h>

#include "PythonBindings.h"
#include "Registers.h"


PyObject *initBindings(void)
{
  Py_Initialize();

  PyObject *tritonModule = Py_InitModule("triton", pythonCallbacks);

  if (tritonModule == NULL) {
    fprintf(stderr, "Failed to initialize Triton bindings\n");
    PyErr_Print();
    exit(1);
  }

  /* Constants register */
  PyModule_AddIntConstant(tritonModule, "ID_RAX",     ID_RAX);
  PyModule_AddIntConstant(tritonModule, "ID_RBX",     ID_RBX);
  PyModule_AddIntConstant(tritonModule, "ID_RCX",     ID_RCX);
  PyModule_AddIntConstant(tritonModule, "ID_RDX",     ID_RDX);
  PyModule_AddIntConstant(tritonModule, "ID_RDI",     ID_RDI);
  PyModule_AddIntConstant(tritonModule, "ID_RSI",     ID_RSI);
  PyModule_AddIntConstant(tritonModule, "ID_RBP",     ID_RBP);
  PyModule_AddIntConstant(tritonModule, "ID_RSP",     ID_RSP);
  PyModule_AddIntConstant(tritonModule, "ID_RIP",     ID_RIP);
  PyModule_AddIntConstant(tritonModule, "ID_R8",      ID_R8);
  PyModule_AddIntConstant(tritonModule, "ID_R9",      ID_R9);
  PyModule_AddIntConstant(tritonModule, "ID_R10",     ID_R10);
  PyModule_AddIntConstant(tritonModule, "ID_R11",     ID_R11);
  PyModule_AddIntConstant(tritonModule, "ID_R12",     ID_R12);
  PyModule_AddIntConstant(tritonModule, "ID_R13",     ID_R13);
  PyModule_AddIntConstant(tritonModule, "ID_R14",     ID_R14);
  PyModule_AddIntConstant(tritonModule, "ID_R15",     ID_R15);
  PyModule_AddIntConstant(tritonModule, "ID_XMM0",    ID_XMM0);
  PyModule_AddIntConstant(tritonModule, "ID_XMM1",    ID_XMM1);
  PyModule_AddIntConstant(tritonModule, "ID_XMM2",    ID_XMM2);
  PyModule_AddIntConstant(tritonModule, "ID_XMM3",    ID_XMM3);
  PyModule_AddIntConstant(tritonModule, "ID_XMM4",    ID_XMM4);
  PyModule_AddIntConstant(tritonModule, "ID_XMM5",    ID_XMM5);
  PyModule_AddIntConstant(tritonModule, "ID_XMM6",    ID_XMM6);
  PyModule_AddIntConstant(tritonModule, "ID_XMM7",    ID_XMM7);
  PyModule_AddIntConstant(tritonModule, "ID_XMM8",    ID_XMM8);
  PyModule_AddIntConstant(tritonModule, "ID_XMM9",    ID_XMM9);
  PyModule_AddIntConstant(tritonModule, "ID_XMM10",   ID_XMM10);
  PyModule_AddIntConstant(tritonModule, "ID_XMM11",   ID_XMM11);
  PyModule_AddIntConstant(tritonModule, "ID_XMM12",   ID_XMM12);
  PyModule_AddIntConstant(tritonModule, "ID_XMM13",   ID_XMM13);
  PyModule_AddIntConstant(tritonModule, "ID_XMM14",   ID_XMM14);
  PyModule_AddIntConstant(tritonModule, "ID_XMM15",   ID_XMM15);

  /* Constants flag */
  PyModule_AddIntConstant(tritonModule, "ID_AF",      ID_AF);
  PyModule_AddIntConstant(tritonModule, "ID_CF",      ID_CF);
  PyModule_AddIntConstant(tritonModule, "ID_DF",      ID_DF);
  PyModule_AddIntConstant(tritonModule, "ID_IF",      ID_IF);
  PyModule_AddIntConstant(tritonModule, "ID_OF",      ID_OF);
  PyModule_AddIntConstant(tritonModule, "ID_PF",      ID_PF);
  PyModule_AddIntConstant(tritonModule, "ID_SF",      ID_SF);
  PyModule_AddIntConstant(tritonModule, "ID_TF",      ID_TF);
  PyModule_AddIntConstant(tritonModule, "ID_ZF",      ID_ZF);

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

