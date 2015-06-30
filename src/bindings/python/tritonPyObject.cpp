
#include <TritonOperand.h>
#include <TritonPyObject.h>
#include <xPyFunc.h>

extern AnalysisProcessor ap;


/*
 * Class SymbolicExpression:
 *
 * - comment (string)
 * - destination (string)
 * - expression (string)
 * - id (integer)
 * - isTainted (bool)
 * - source (string)
 */
PyObject *PySymbolicExpression(SymbolicExpression *expression)
{
  if (expression == nullptr)
    return Py_None;

  PyObject *dictSEClass = xPyDict_New();
  PyDict_SetItemString(dictSEClass, "source",       PyString_FromFormat("%s", expression->getSource()->str().c_str()));
  PyDict_SetItemString(dictSEClass, "destination",  PyString_FromFormat("%s", expression->getDestination()->str().c_str()));
  PyDict_SetItemString(dictSEClass, "expression",   PyString_FromFormat("%s", expression->getExpression()->str().c_str()));

  PyObject *comment = Py_None;
  if (expression->getComment()->empty() == false)
    comment = PyString_FromFormat("%s", expression->getComment()->c_str());

  PyDict_SetItemString(dictSEClass, "comment",      comment);
  PyDict_SetItemString(dictSEClass, "id",           PyLong_FromLong(expression->getID()));
  PyDict_SetItemString(dictSEClass, "isTainted",    PyBool_FromLong(expression->isTainted));

  PyObject *SEClassName = xPyString_FromString("SymbolicExpression");
  PyObject *SEClass = xPyClass_New(nullptr, dictSEClass, SEClassName);

  Py_DECREF(dictSEClass);
  Py_DECREF(SEClassName);
  Py_INCREF(SEClass);

  return SEClass;
}


/*
 * Class SymbolicVariable:
 *
 * - id (integer)
 * - kind (IDREF.SYMVAR)
 * - kindValue (IDREG.REG or integer, it depends of the kind)
 * - name (string)
 * - size (integer)
 * - comment(string)
 */
PyObject *PySymbolicVariable(SymbolicVariable *symVar)
{
  if (symVar == nullptr)
    return Py_None;

  PyObject *dictSVClass = xPyDict_New();
  PyDict_SetItemString(dictSVClass, "id",        PyLong_FromLong(symVar->getSymVarId()));
  PyDict_SetItemString(dictSVClass, "kind",      PyLong_FromLong(symVar->getSymVarKind()));
  PyDict_SetItemString(dictSVClass, "kindValue", PyLong_FromLong(symVar->getSymVarKindValue()));
  PyDict_SetItemString(dictSVClass, "name",      PyString_FromFormat("%s", symVar->getSymVarName().c_str()));
  PyDict_SetItemString(dictSVClass, "size",      PyLong_FromLong(symVar->getSymVarSize()));

  PyObject *comment = Py_None;
  if (symVar->getSymVarComment().empty() == false)
    comment = PyString_FromFormat("%s", symVar->getSymVarComment().c_str());

  PyDict_SetItemString(dictSVClass, "comment", comment);

  PyObject *SVClassName = xPyString_FromString("SymbolicVariable");
  PyObject *SVClass = xPyClass_New(nullptr, dictSVClass, SVClassName);

  Py_DECREF(dictSVClass);
  Py_DECREF(SVClassName);
  Py_INCREF(SVClass);

  return SVClass;
}


/*
 * Class Instruction:
 *
 * - address (integer)
 * - assembly (string)
 * - baseAddress (integer)
 * - imageName (string)
 * - isBranch (bool)
 * - offset (integer)
 * - opcode (integer)
 * - opcodeCategory (IDREF.OPCODE_CATEGORY)
 * - operands ([Operand])
 * - routineName (string)
 * - sectionName (string)
 * - symbolicExpressions (list of SymbolicExpression)
 * - threadId (integer)
 */
PyObject *PyInstruction(Inst *inst)
{
  if (inst == nullptr)
    return Py_None;

  /* Create the class dictionary */
  PyObject *dictInstClass = xPyDict_New();
  PyDict_SetItemString(dictInstClass, "address",        PyLong_FromLong(inst->getAddress()));
  PyDict_SetItemString(dictInstClass, "assembly",       PyString_FromFormat("%s", inst->getDisassembly().c_str()));
  PyDict_SetItemString(dictInstClass, "baseAddress",    PyLong_FromLong(inst->getBaseAddress()));
  PyDict_SetItemString(dictInstClass, "imageName",      PyString_FromFormat("%s", inst->getImageName().c_str()));
  PyDict_SetItemString(dictInstClass, "isBranch",       PyBool_FromLong(inst->isBranch()));
  PyDict_SetItemString(dictInstClass, "offset",         PyLong_FromLong(inst->getOffset()));
  PyDict_SetItemString(dictInstClass, "opcode",         PyLong_FromLong(inst->getOpcode()));
  PyDict_SetItemString(dictInstClass, "opcodeCategory", PyLong_FromLong(inst->getOpcodeCategory()));
  PyDict_SetItemString(dictInstClass, "routineName",    PyString_FromFormat("%s", inst->getRoutineName().c_str()));
  PyDict_SetItemString(dictInstClass, "sectionName",    PyString_FromFormat("%s", inst->getSectionName().c_str()));
  PyDict_SetItemString(dictInstClass, "threadId",       PyLong_FromLong(inst->getThreadID()));

  /* Setup the symbolic expression list */
  PyObject *SEList                          = xPyList_New(inst->numberOfExpressions());
  std::list<SymbolicExpression*> symExpressions   = inst->getSymbolicExpressions();
  std::list<SymbolicExpression*>::iterator it1 = symExpressions.begin();

  Py_ssize_t index = 0;
  for ( ; it1 != symExpressions.end(); it1++){
    PyObject *PySE = PySymbolicExpression(*it1);
    PyList_SetItem(SEList, index, PySE);
    Py_DECREF(PySE);
    index++;
  }

  PyDict_SetItemString(dictInstClass, "symbolicExpressions", SEList);

  /* Setup the operands list */
  std::vector<TritonOperand> operands = inst->getOperands();
  std::vector<TritonOperand>::iterator it2 = operands.begin();
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
 * - baseAddress (integer)
 * - imageName (string)
 * - isBranch (bool)
 * - offset (integer)
 * - opcode (integer)
 * - opcodeCategory (IDREF.OPCODE_CATEGORY)
 * - operands ([Operand])
 * - routineName (string)
 * - sectionName (string)
 * - symbolicExpressions (list of SymbolicExpression)
 * - threadId (integer)
 */
PyObject *PyInstruction(IRBuilder *irb)
{
  if (irb == nullptr)
    return Py_None;

  PyObject *dictInstClass = xPyDict_New();
  PyDict_SetItemString(dictInstClass, "address",        PyLong_FromLong(irb->getAddress()));
  PyDict_SetItemString(dictInstClass, "assembly",       PyString_FromFormat("%s", irb->getDisassembly().c_str()));
  PyDict_SetItemString(dictInstClass, "baseAddress",    PyLong_FromLong(irb->getBaseAddress()));
  PyDict_SetItemString(dictInstClass, "imageName",      PyString_FromFormat("%s", irb->getImageName().c_str()));
  PyDict_SetItemString(dictInstClass, "isBranch",       PyBool_FromLong(irb->isBranch()));
  PyDict_SetItemString(dictInstClass, "offset",         PyLong_FromLong(irb->getOffset()));
  PyDict_SetItemString(dictInstClass, "opcode",         PyLong_FromLong(irb->getOpcode()));
  PyDict_SetItemString(dictInstClass, "opcodeCategory", PyLong_FromLong(irb->getOpcodeCategory()));
  PyDict_SetItemString(dictInstClass, "routineName",    PyString_FromFormat("%s", irb->getRoutineName().c_str()));
  PyDict_SetItemString(dictInstClass, "sectionName",    PyString_FromFormat("%s", irb->getSectionName().c_str()));
  PyDict_SetItemString(dictInstClass, "threadId",       PyLong_FromLong(irb->getThreadID()));

  /* Before the processing, the symbolic expression list is empty */
  PyObject *SEList = xPyList_New(0);
  PyDict_SetItemString(dictInstClass, "symbolicExpressions", SEList);
  Py_DECREF(SEList);

  /* Setup the operands list */
  std::vector<TritonOperand> operands = irb->getOperands();
  std::vector<TritonOperand>::iterator it = operands.begin();
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


PyObject *PyOperand(TritonOperand operand)
{
  PyObject *dictOperandClass = xPyDict_New();
  PyDict_SetItemString(dictOperandClass, "baseReg",       PyLong_FromLong(operand.getBaseReg()));
  PyDict_SetItemString(dictOperandClass, "displacement",  PyLong_FromLong(operand.getDisplacement()));
  PyDict_SetItemString(dictOperandClass, "indexReg",      PyLong_FromLong(operand.getIndexReg()));
  PyDict_SetItemString(dictOperandClass, "memoryScale",   PyLong_FromLong(operand.getMemoryScale()));
  PyDict_SetItemString(dictOperandClass, "size",          PyLong_FromLong(operand.getSize()));
  PyDict_SetItemString(dictOperandClass, "type",          PyLong_FromLong(operand.getType()));
  PyDict_SetItemString(dictOperandClass, "value",         PyLong_FromLong(operand.getValue()));

  /* Create the Operand class */
  PyObject *operandClassName = xPyString_FromString("Operand");
  PyObject *operandClass  = xPyClass_New(nullptr, dictOperandClass, operandClassName);

  Py_DECREF(dictOperandClass);
  Py_DECREF(operandClassName);
  Py_INCREF(operandClass);

  return operandClass;
}

