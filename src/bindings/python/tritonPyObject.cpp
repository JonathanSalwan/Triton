
#include "TritonPyObject.h"
#include "pin.H"
#include "xPyFunc.h"


/*
 * Class SymbolicElement:
 *
 * - source (string)
 * - destination (string)
 * - expression (string)
 * - id (integer)
 * - isTainted (bool)
 */
PyObject *PySymbolicElement(SymbolicElement *element)
{
  PyObject *dictSEClass = xPyDict_New();
  PyDict_SetItemString(dictSEClass, "source",       PyString_FromFormat("%s", element->getSource()->str().c_str()));
  PyDict_SetItemString(dictSEClass, "destination",  PyString_FromFormat("%s", element->getDestination()->str().c_str()));
  PyDict_SetItemString(dictSEClass, "expression",   PyString_FromFormat("%s", element->getExpression()->str().c_str()));
  PyDict_SetItemString(dictSEClass, "id",           PyInt_FromLong(element->getID()));
  PyDict_SetItemString(dictSEClass, "isTainted",    PyBool_FromLong(element->isTainted));

  PyObject *SEClassName = xPyString_FromString("SymbolicElement");
  PyObject *SEClass  = xPyClass_New(NULL, dictSEClass, SEClassName);

  Py_DECREF(dictSEClass);
  Py_DECREF(SEClassName);
  Py_INCREF(SEClass);

  return SEClass;
}


/*
 * Class Instruction:
 *
 * - address (integer)
 * - assembly (string)
 * - isBranch (bool)
 * - opcode (integer)
 * - opcodeCategory (IDREF.OPCODE_CATEGORY)
 * - symbolicElements (list of SymbolicElement)
 * - routineName (string)
 * - threadId (integer)
 */
PyObject *PyInstruction(Inst *inst)
{
  /* Create the class dictionary */
  PyObject *dictInstClass = xPyDict_New();
  PyDict_SetItemString(dictInstClass, "address",        PyInt_FromLong(inst->getAddress()));
  PyDict_SetItemString(dictInstClass, "assembly",       PyString_FromFormat("%s", inst->getDisassembly().c_str()));
  PyDict_SetItemString(dictInstClass, "isBranch",       PyBool_FromLong(inst->isBranch()));
  PyDict_SetItemString(dictInstClass, "opcode",         PyInt_FromLong(inst->getOpcode()));
  PyDict_SetItemString(dictInstClass, "opcodeCategory", PyInt_FromLong(inst->getOpcodeCategory()));
  PyDict_SetItemString(dictInstClass, "routineName",    PyString_FromFormat("%s", RTN_FindNameByAddress(inst->getAddress()).c_str()));
  PyDict_SetItemString(dictInstClass, "threadId",       PyInt_FromLong(inst->getThreadID()));

  /* Setup the symbolic element list */
  PyObject *SEList                         = xPyList_New(inst->numberOfElements());
  std::list<SymbolicElement*> symElements  = inst->getSymbolicElements();
  std::list<SymbolicElement*>::iterator it = symElements.begin();

  Py_ssize_t index = 0;
  for ( ; it != symElements.end(); it++){
    PyObject *PySE = PySymbolicElement(*it);
    PyList_SetItem(SEList, index, PySE);
    Py_DECREF(PySE);
    index++;
  }

  PyDict_SetItemString(dictInstClass, "symbolicElements", SEList);

  /* Create the Instruction class */
  PyObject *instClassName = xPyString_FromString("Instruction");
  PyObject *instClass  = xPyClass_New(NULL, dictInstClass, instClassName);

  Py_DECREF(dictInstClass);
  Py_DECREF(instClassName);

  return instClass;
}


/*
 * Class Instruction:
 *
 * - address (integer)
 * - assembly (string)
 * - isBranch (bool)
 * - opcode (integer)
 * - opcodeCategory (IDREF.OPCODE_CATEGORY)
 * - symbolicElements (list of SymbolicElement)
 * - routineName (string)
 * - threadId (integer)
 */
PyObject *PyInstruction(IRBuilder *irb)
{
  PyObject *dictInstClass = xPyDict_New();
  PyDict_SetItemString(dictInstClass, "address",        PyInt_FromLong(irb->getAddress()));
  PyDict_SetItemString(dictInstClass, "assembly",       PyString_FromFormat("%s", irb->getDisassembly().c_str()));
  PyDict_SetItemString(dictInstClass, "isBranch",       PyBool_FromLong(irb->isBranch()));
  PyDict_SetItemString(dictInstClass, "opcode",         PyInt_FromLong(irb->getOpcode()));
  PyDict_SetItemString(dictInstClass, "opcodeCategory", PyInt_FromLong(irb->getOpcodeCategory()));
  PyDict_SetItemString(dictInstClass, "routineName",    PyString_FromFormat("%s", RTN_FindNameByAddress(irb->getAddress()).c_str()));
  PyDict_SetItemString(dictInstClass, "threadId",       PyInt_FromLong(irb->getThreadID()));

  /* Before the processing, the symbolic element list is empty */
  PyObject *SEList = xPyList_New(0);
  PyDict_SetItemString(dictInstClass, "symbolicElements", SEList);
  Py_DECREF(SEList);

  /* Create the Instruction class */
  PyObject *instClassName = xPyString_FromString("Instruction");
  PyObject *instClass  = xPyClass_New(NULL, dictInstClass, instClassName);

  Py_DECREF(dictInstClass);
  Py_DECREF(instClassName);

  return instClass;
}

