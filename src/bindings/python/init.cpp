
#include <iostream>
#include <python2.7/Python.h>

#include "SymbolicEngine.h"
#include "PythonBindings.h"
#include "xPyFunc.h"

void initFlagEnv(PyObject *);
void initOpcodeCategoryEnv(PyObject *);
void initOpcodeEnv(PyObject *);
void initOperandEnv(PyObject *);
void initRegEnv(PyObject *);


/*
 * Triton: [IDREF, callback, CB_AFTER, CB_BEFORE]
 * IDREF: [REG, FLAG, OPCODE]
 * REG: [RAX, RBX, XMM0, ...]
 * FLAG: [AF, OF, ZF, ...]
 * OPCODE: [AAA, MOV, MOVSX, XOR, ...]
 * OPERAND: [IMM, REG, MEM_R, MEM_W]
 * OPCODE_CATEGORY: [XED_CATEGORY_AES, XED_CATEGORY_CMOV, ...]
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


  // REG ---------------------

  /* Create the IDREF.REG class */
  PyObject *idRegClassName = xPyString_FromString("REG");
  PyObject *idRegClassDict = xPyDict_New();

  /* Add registers ref into IDREF.REG class */
  initRegEnv(idRegClassDict);

  /* Create the REG class */
  PyObject *idRegClass = xPyClass_New(NULL, idRegClassDict, idRegClassName);

  // REG ---------------------


  // FLAG ---------------------

  /* Create the IDREF.FLAG class */
  PyObject *idFlagClassName = xPyString_FromString("FLAG");
  PyObject *idFlagClassDict = xPyDict_New();

  /* Add flags ref into IDREF.FLAG class */
  initFlagEnv(idFlagClassDict);

  /* Create the FLAG class */
  PyObject *idFlagClass = xPyClass_New(NULL, idFlagClassDict, idFlagClassName);

  // FLAG ---------------------


  // OPCODE ---------------------

  /* Create the IDREF.OPCODE class */
  PyObject *idOpcodeClassName = xPyString_FromString("OPCODE");
  PyObject *idOpcodeClassDict = xPyDict_New();

  /* Add registers ref into IDREF.OPCODE class */
  initOpcodeEnv(idOpcodeClassDict);

  /* Create the OPCODE class */
  PyObject *idOpcodeClass = xPyClass_New(NULL, idOpcodeClassDict, idOpcodeClassName);

  // OPCODE ---------------------


  // OPCODE_CATEGORY ---------------------

  /* Create the IDREF.OPCODE_CATEGORY class */
  PyObject *idOpcodeCategoryClassName = xPyString_FromString("OPCODE_CATEGORY");
  PyObject *idOpcodeCategoryClassDict = xPyDict_New();

  /* Add registers ref into IDREF.OPCODE_CATEGORY class */
  initOpcodeCategoryEnv(idOpcodeCategoryClassDict);

  /* Create the OPCODE_CATEGORY class */
  PyObject *idOpcodeCategoryClass = xPyClass_New(NULL, idOpcodeCategoryClassDict, idOpcodeCategoryClassName);

  // OPCODE_CATEGORY ---------------------


  // OPERAND ---------------------

  /* Create the IDREF.OPERAND class */
  PyObject *idOperandClassName = xPyString_FromString("OPERAND");
  PyObject *idOperandClassDict = xPyDict_New();

  /* Add registers ref into IDREF.OPERAND class */
  initOperandEnv(idOperandClassDict);

  /* Create the OPCODE class */
  PyObject *idOperandClass = xPyClass_New(NULL, idOperandClassDict, idOperandClassName);

  // OPERAND ---------------------


  /* Add REG, FLAG, OPCODE, OPCODE_CATEGORY, OPERAND into IDREF */
  PyDict_SetItemString(idRefClassDict, "FLAG", idFlagClass);
  PyDict_SetItemString(idRefClassDict, "OPCODE", idOpcodeClass);
  PyDict_SetItemString(idRefClassDict, "OPCODE_CATEGORY", idOpcodeCategoryClass);
  PyDict_SetItemString(idRefClassDict, "OPERAND", idOperandClass);
  PyDict_SetItemString(idRefClassDict, "REG", idRegClass);

  /* Create the IDREF class */
  PyObject *idRefClass = xPyClass_New(NULL, idRefClassDict, idRefClassName);

  /* add IDREF into triton module */
  PyModule_AddObject(tritonModule, "IDREF", idRefClass);

  /* Constants Triton internal */
  PyModule_AddIntConstant(tritonModule, "CB_BEFORE",  CB_BEFORE);
  PyModule_AddIntConstant(tritonModule, "CB_AFTER",   CB_AFTER);
  PyModule_AddObject(tritonModule,      "UNSET",      Py_BuildValue("k", UNSET)); // Py_BuildValue for unsigned long

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

