
#include "TritonPyObject.h"
#include "pin.H"
#include "xPyFunc.h"


/*
 * Class SymbolicElement:
 *
 * - comment (string)
 * - destination (string)
 * - expression (string)
 * - id (integer)
 * - isTainted (bool)
 * - source (string)
 */
PyObject *PySymbolicElement(SymbolicElement *element)
{
  PyObject *dictSEClass = xPyDict_New();
  PyDict_SetItemString(dictSEClass, "source",       PyString_FromFormat("%s", element->getSource()->str().c_str()));
  PyDict_SetItemString(dictSEClass, "destination",  PyString_FromFormat("%s", element->getDestination()->str().c_str()));
  PyDict_SetItemString(dictSEClass, "expression",   PyString_FromFormat("%s", element->getExpression()->str().c_str()));

  PyObject *comment = Py_None;
  if (element->getComment()->empty() == false)
    comment = PyString_FromFormat("%s", element->getComment()->c_str());

  PyDict_SetItemString(dictSEClass, "comment",      comment);
  PyDict_SetItemString(dictSEClass, "id",           PyInt_FromLong(element->getID()));
  PyDict_SetItemString(dictSEClass, "isTainted",    PyBool_FromLong(element->isTainted));

  PyObject *SEClassName = xPyString_FromString("SymbolicElement");
  PyObject *SEClass  = xPyClass_New(nullptr, dictSEClass, SEClassName);

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
 * - imageName (string)
 * - isBranch (bool)
 * - opcode (integer)
 * - opcodeCategory (IDREF.OPCODE_CATEGORY)
 * - operands ([Operand])
 * - symbolicElements (list of SymbolicElement)
 * - routineName (string)
 * - sectionName (string)
 * - threadId (integer)
 */
PyObject *PyInstruction(Inst *inst)
{
  /* Create the class dictionary */
  PyObject *dictInstClass = xPyDict_New();
  PIN_LockClient();
  PyDict_SetItemString(dictInstClass, "address",        PyInt_FromLong(inst->getAddress()));
  PyDict_SetItemString(dictInstClass, "assembly",       PyString_FromFormat("%s", inst->getDisassembly().c_str()));
  PyDict_SetItemString(dictInstClass, "imageName",      PyString_FromFormat("%s", IMG_Name(SEC_Img(RTN_Sec(RTN_FindByAddress(inst->getAddress())))).c_str()));
  PyDict_SetItemString(dictInstClass, "isBranch",       PyBool_FromLong(inst->isBranch()));
  PyDict_SetItemString(dictInstClass, "opcode",         PyInt_FromLong(inst->getOpcode()));
  PyDict_SetItemString(dictInstClass, "opcodeCategory", PyInt_FromLong(inst->getOpcodeCategory()));
  PyDict_SetItemString(dictInstClass, "routineName",    PyString_FromFormat("%s", RTN_FindNameByAddress(inst->getAddress()).c_str()));
  PyDict_SetItemString(dictInstClass, "sectionName",    PyString_FromFormat("%s", SEC_Name(RTN_Sec(RTN_FindByAddress(inst->getAddress()))).c_str()));
  PyDict_SetItemString(dictInstClass, "threadId",       PyInt_FromLong(inst->getThreadID()));
  PIN_UnlockClient();


  /* Setup the symbolic element list */
  PyObject *SEList                          = xPyList_New(inst->numberOfElements());
  std::list<SymbolicElement*> symElements   = inst->getSymbolicElements();
  std::list<SymbolicElement*>::iterator it1 = symElements.begin();

  Py_ssize_t index = 0;
  for ( ; it1 != symElements.end(); it1++){
    PyObject *PySE = PySymbolicElement(*it1);
    PyList_SetItem(SEList, index, PySE);
    Py_DECREF(PySE);
    index++;
  }

  PyDict_SetItemString(dictInstClass, "symbolicElements", SEList);


  /* Setup the operands list */
  std::vector< std::tuple<IRBuilderOperand::operand_t, uint64_t, uint32_t, uint64_t, uint64_t, uint64_t, uint64_t> > operands = inst->getOperands();
  std::vector< std::tuple<IRBuilderOperand::operand_t, uint64_t, uint32_t, uint64_t, uint64_t, uint64_t, uint64_t> >::iterator it2 = operands.begin();
  PyObject *OperandList = xPyList_New(operands.size());

  index = 0;
  for ( ; it2 != operands.end(); it2++){
    PyObject *operand = PyOperand(*it2);
    PyList_SetItem(OperandList, index, operand);
    Py_DECREF(operand);
    index++;
  }

  PyDict_SetItemString(dictInstClass, "operands", OperandList);


  /* Create the Instruction class */
  PyObject *instClassName = xPyString_FromString("Instruction");
  PyObject *instClass  = xPyClass_New(nullptr, dictInstClass, instClassName);

  Py_DECREF(dictInstClass);
  Py_DECREF(instClassName);

  return instClass;
}


/*
 * Class Instruction:
 *
 * - address (integer)
 * - assembly (string)
 * - imageName (string)
 * - isBranch (bool)
 * - opcode (integer)
 * - opcodeCategory (IDREF.OPCODE_CATEGORY)
 * - operands ([Operand])
 * - symbolicElements (list of SymbolicElement)
 * - routineName (string)
 * - sectionName (string)
 * - threadId (integer)
 */
PyObject *PyInstruction(IRBuilder *irb)
{
  PyObject *dictInstClass = xPyDict_New();
  PIN_LockClient();
  PyDict_SetItemString(dictInstClass, "address",        PyInt_FromLong(irb->getAddress()));
  PyDict_SetItemString(dictInstClass, "assembly",       PyString_FromFormat("%s", irb->getDisassembly().c_str()));
  PyDict_SetItemString(dictInstClass, "imageName",      PyString_FromFormat("%s", IMG_Name(SEC_Img(RTN_Sec(RTN_FindByAddress(irb->getAddress())))).c_str()));
  PyDict_SetItemString(dictInstClass, "isBranch",       PyBool_FromLong(irb->isBranch()));
  PyDict_SetItemString(dictInstClass, "opcode",         PyInt_FromLong(irb->getOpcode()));
  PyDict_SetItemString(dictInstClass, "opcodeCategory", PyInt_FromLong(irb->getOpcodeCategory()));
  PyDict_SetItemString(dictInstClass, "routineName",    PyString_FromFormat("%s", RTN_FindNameByAddress(irb->getAddress()).c_str()));
  PyDict_SetItemString(dictInstClass, "sectionName",    PyString_FromFormat("%s", SEC_Name(RTN_Sec(RTN_FindByAddress(irb->getAddress()))).c_str()));
  PyDict_SetItemString(dictInstClass, "threadId",       PyInt_FromLong(irb->getThreadID()));
  PIN_UnlockClient();


  /* Before the processing, the symbolic element list is empty */
  PyObject *SEList = xPyList_New(0);
  PyDict_SetItemString(dictInstClass, "symbolicElements", SEList);
  Py_DECREF(SEList);


  /* Setup the operands list */
  std::vector< std::tuple<IRBuilderOperand::operand_t, uint64_t, uint32_t, uint64_t, uint64_t, uint64_t, uint64_t> > operands = irb->getOperands();
  std::vector< std::tuple<IRBuilderOperand::operand_t, uint64_t, uint32_t, uint64_t, uint64_t, uint64_t, uint64_t> >::iterator it = operands.begin();
  PyObject *OperandList = xPyList_New(operands.size());

  Py_ssize_t index = 0;
  for ( ; it != operands.end(); it++){
    PyObject *operand = PyOperand(*it);
    PyList_SetItem(OperandList, index, operand);
    Py_DECREF(operand);
    index++;
  }

  PyDict_SetItemString(dictInstClass, "operands", OperandList);


  /* Create the Instruction class */
  PyObject *instClassName = xPyString_FromString("Instruction");
  PyObject *instClass  = xPyClass_New(nullptr, dictInstClass, instClassName);

  Py_DECREF(dictInstClass);
  Py_DECREF(instClassName);

  return instClass;
}


PyObject *PyOperand(std::tuple<IRBuilderOperand::operand_t, uint64_t, uint32_t, uint64_t, uint64_t, uint64_t, uint64_t> operand)
{
  PyObject *dictOperandClass = xPyDict_New();
  PyDict_SetItemString(dictOperandClass, "type",          PyLong_FromLong(std::get<0>(operand)));
  PyDict_SetItemString(dictOperandClass, "value",         PyLong_FromLong(std::get<1>(operand)));
  PyDict_SetItemString(dictOperandClass, "size",          PyLong_FromLong(std::get<2>(operand)));
  PyDict_SetItemString(dictOperandClass, "displacement",  PyLong_FromLong(std::get<3>(operand)));
  PyDict_SetItemString(dictOperandClass, "baseReg",       PyLong_FromLong(std::get<4>(operand)));
  PyDict_SetItemString(dictOperandClass, "indexReg",      PyLong_FromLong(std::get<5>(operand)));
  PyDict_SetItemString(dictOperandClass, "memoryScale",   PyLong_FromLong(std::get<6>(operand)));

  /* Create the Operand class */
  PyObject *operandClassName = xPyString_FromString("Operand");
  PyObject *operandClass  = xPyClass_New(nullptr, dictOperandClass, operandClassName);

  Py_DECREF(dictOperandClass);
  Py_DECREF(operandClassName);
  Py_INCREF(operandClass);

  return operandClass;
}

