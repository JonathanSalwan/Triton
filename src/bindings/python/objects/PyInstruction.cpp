/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <TritonPyObject.h>
#include <xPyFunc.h>

/*
 * Class Instruction
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


void Instruction_dealloc(PyObject *self) {
  Py_DECREF(self);
}


static PyObject *Instruction_str(Instruction_Object *obj)
{
  if (PyInstruction_AsIns(obj) != nullptr)
    return PyString_FromFormat("%s", PyInstruction_AsIns(obj)->getDisassembly().c_str());
  return PyString_FromFormat("%s", PyInstruction_AsIrb(obj)->getDisassembly().c_str());
}


static char Instruction_getAddress_doc[] = "Returns the address";
static PyObject *Instruction_getAddress(PyObject *self, PyObject *noarg)
{
  if (PyInstruction_AsIns(self) != nullptr)
    return Py_BuildValue("k", PyInstruction_AsIns(self)->getAddress());
  return Py_BuildValue("k", PyInstruction_AsIrb(self)->getAddress());
}


static char Instruction_getDisassembly_doc[] = "Returns the disassembly";
static PyObject *Instruction_getDisassembly(PyObject *self, PyObject *noarg)
{
  if (PyInstruction_AsIns(self) != nullptr)
    return PyString_FromFormat("%s", PyInstruction_AsIns(self)->getDisassembly().c_str());
  return PyString_FromFormat("%s", PyInstruction_AsIrb(self)->getDisassembly().c_str());
}


static char Instruction_getBaseAddress_doc[] = "Returns the base address";
static PyObject *Instruction_getBaseAddress(PyObject *self, PyObject *noarg)
{
  if (PyInstruction_AsIns(self) != nullptr)
    return Py_BuildValue("k", PyInstruction_AsIns(self)->getBaseAddress());
  return Py_BuildValue("k", PyInstruction_AsIrb(self)->getBaseAddress());
}


static char Instruction_getImageName_doc[] = "Returns the current image name";
static PyObject *Instruction_getImageName(PyObject *self, PyObject *noarg)
{
  if (PyInstruction_AsIns(self) != nullptr)
    return PyString_FromFormat("%s", PyInstruction_AsIns(self)->getImageName().c_str());
  return PyString_FromFormat("%s", PyInstruction_AsIrb(self)->getImageName().c_str());
}


static char Instruction_getOffset_doc[] = "Returns the offset";
static PyObject *Instruction_getOffset(PyObject *self, PyObject *noarg)
{
  if (PyInstruction_AsIns(self) != nullptr)
    return Py_BuildValue("k", PyInstruction_AsIns(self)->getOffset());
  return Py_BuildValue("k", PyInstruction_AsIrb(self)->getOffset());
}


static char Instruction_getOpcode_doc[] = "Returns the base opcode";
static PyObject *Instruction_getOpcode(PyObject *self, PyObject *noarg)
{
  if (PyInstruction_AsIns(self) != nullptr)
    return Py_BuildValue("k", PyInstruction_AsIns(self)->getOpcode());
  return Py_BuildValue("k", PyInstruction_AsIrb(self)->getOpcode());
}


static char Instruction_getOpcodeCategory_doc[] = "Returns the base address";
static PyObject *Instruction_getOpcodeCategory(PyObject *self, PyObject *noarg)
{
  if (PyInstruction_AsIns(self) != nullptr)
    return Py_BuildValue("k", PyInstruction_AsIns(self)->getOpcodeCategory());
  return Py_BuildValue("k", PyInstruction_AsIrb(self)->getOpcodeCategory());
}


static char Instruction_getOperands_doc[] = "Returns the operands";
static PyObject *Instruction_getOperands(PyObject *self, PyObject *noarg)
{
  std::vector<TritonOperand> operands;
  std::vector<TritonOperand>::iterator it;

  if (PyInstruction_AsIns(self) != nullptr)
    operands = PyInstruction_AsIns(self)->getOperands();
  else
    operands = PyInstruction_AsIrb(self)->getOperands();

  PyObject *OperandList = xPyList_New(operands.size());
  Py_ssize_t index = 0;

  for (it = operands.begin() ; it != operands.end(); it++) {
    PyObject *operand = PyOperand(*it);
    PyList_SetItem(OperandList, index, operand);
    Py_DECREF(operand);
    index++;
  }
  return OperandList;
}


static char Instruction_getRoutineName_doc[] = "Returns the current routine name";
static PyObject *Instruction_getRoutineName(PyObject *self, PyObject *noarg)
{
  if (PyInstruction_AsIns(self) != nullptr)
    return PyString_FromFormat("%s", PyInstruction_AsIns(self)->getRoutineName().c_str());
  return PyString_FromFormat("%s", PyInstruction_AsIrb(self)->getRoutineName().c_str());
}


static char Instruction_getSectionName_doc[] = "Returns the current section name";
static PyObject *Instruction_getSectionName(PyObject *self, PyObject *noarg)
{
  if (PyInstruction_AsIns(self) != nullptr)
    return PyString_FromFormat("%s", PyInstruction_AsIns(self)->getSectionName().c_str());
  return PyString_FromFormat("%s", PyInstruction_AsIrb(self)->getSectionName().c_str());
}


static char Instruction_getSymbolicExpressions_doc[] = "Returns the symbolic expressions";
static PyObject *Instruction_getSymbolicExpressions(PyObject *self, PyObject *noarg)
{
  std::list<SymbolicExpression*> symExpressions;
  std::list<SymbolicExpression*>::iterator it;

  if (PyInstruction_AsIns(self) != nullptr) {
    symExpressions = PyInstruction_AsIns(self)->getSymbolicExpressions();
  }

  PyObject *SEList = xPyList_New(symExpressions.size());
  Py_ssize_t index = 0;
  for (it = symExpressions.begin() ; it != symExpressions.end(); it++) {
    PyObject *PySE = PySymbolicExpression(*it);
    PyList_SetItem(SEList, index, PySE);
    Py_DECREF(PySE);
    index++;
  }

  return SEList;
}


static char Instruction_getThreadId_doc[] = "Returns the thread id";
static PyObject *Instruction_getThreadId(PyObject *self, PyObject *noarg)
{
  if (PyInstruction_AsIns(self) != nullptr)
    return Py_BuildValue("k", PyInstruction_AsIns(self)->getThreadID());
  return Py_BuildValue("k", PyInstruction_AsIrb(self)->getThreadID());
}


static char Instruction_isBranch_doc[] = "Returns true or false if it is a branch instruction";
static PyObject *Instruction_isBranch(PyObject *self, PyObject *noarg)
{
  if (PyInstruction_AsIns(self) != nullptr)
    return PyBool_FromLong(PyInstruction_AsIns(self)->isBranch());
  return PyBool_FromLong(PyInstruction_AsIrb(self)->isBranch());
}


PyMethodDef Instruction_callbacks[] = {
  {"getAddress",                Instruction_getAddress,             METH_NOARGS,   Instruction_getAddress_doc},
  {"getDisassembly",            Instruction_getDisassembly,         METH_NOARGS,   Instruction_getDisassembly_doc},
  {"getBaseAddress",            Instruction_getBaseAddress,         METH_NOARGS,   Instruction_getBaseAddress_doc},
  {"getImageName",              Instruction_getImageName,           METH_NOARGS,   Instruction_getImageName_doc},
  {"getOffset",                 Instruction_getOffset,              METH_NOARGS,   Instruction_getOffset_doc},
  {"getOpcode",                 Instruction_getOpcode,              METH_NOARGS,   Instruction_getOpcode_doc},
  {"getOpcodeCategory",         Instruction_getOpcodeCategory,      METH_NOARGS,   Instruction_getOpcodeCategory_doc},
  {"getOperands",               Instruction_getOperands,            METH_NOARGS,   Instruction_getOperands_doc},
  {"getRoutineName",            Instruction_getRoutineName,         METH_NOARGS,   Instruction_getRoutineName_doc},
  {"getSectionName",            Instruction_getSectionName,         METH_NOARGS,   Instruction_getSectionName_doc},
  {"getSymbolicExpressions",    Instruction_getSymbolicExpressions, METH_NOARGS,   Instruction_getSymbolicExpressions_doc},
  {"getThreadId",               Instruction_getThreadId,            METH_NOARGS,   Instruction_getThreadId_doc},
  {"isBranch",                  Instruction_isBranch,               METH_NOARGS,   Instruction_isBranch_doc},
  {nullptr,                     nullptr,                            0,             nullptr}
};


PyTypeObject Instruction_Type = {
    PyObject_HEAD_INIT(&PyType_Type)
    0,                                          /* ob_size*/
    "Instruction",                              /* tp_name*/
    sizeof(Instruction_Object),                 /* tp_basicsize*/
    0,                                          /* tp_itemsize*/
    (destructor)Instruction_dealloc,            /* tp_dealloc*/
    0,                                          /* tp_print*/
    0,                                          /* tp_getattr*/
    0,                                          /* tp_setattr*/
    0,                                          /* tp_compare*/
    0,                                          /* tp_repr*/
    0,                                          /* tp_as_number*/
    0,                                          /* tp_as_sequence*/
    0,                                          /* tp_as_mapping*/
    0,                                          /* tp_hash */
    0,                                          /* tp_call*/
    (reprfunc)Instruction_str,                  /* tp_str*/
    0,                                          /* tp_getattro*/
    0,                                          /* tp_setattro*/
    0,                                          /* tp_as_buffer*/
    Py_TPFLAGS_DEFAULT,                         /* tp_flags*/
    "Instruction objects",                      /* tp_doc */
    0,                                          /* tp_traverse */
    0,                                          /* tp_clear */
    0,                                          /* tp_richcompare */
    0,                                          /* tp_weaklistoffset */
    0,                                          /* tp_iter */
    0,                                          /* tp_iternext */
    Instruction_callbacks,                      /* tp_methods */
    0,                                          /* tp_members */
    0,                                          /* tp_getset */
    0,                                          /* tp_base */
    0,                                          /* tp_dict */
    0,                                          /* tp_descr_get */
    0,                                          /* tp_descr_set */
    0,                                          /* tp_dictoffset */
    0,                                          /* tp_init */
    0,                                          /* tp_alloc */
    0,                                          /* tp_new */
};


PyObject *PyInstruction(Inst *inst)
{
  Instruction_Object *object;

  PyType_Ready(&Instruction_Type);
  object = PyObject_NEW(Instruction_Object, &Instruction_Type);
  if (object != NULL) {
    object->irb = nullptr;
    object->ins = inst;
  }

  return (PyObject *)object;
}


PyObject *PyInstruction(IRBuilder *irb)
{
  Instruction_Object *object;

  PyType_Ready(&Instruction_Type);
  object = PyObject_NEW(Instruction_Object, &Instruction_Type);
  if (object != NULL) {
    object->irb = irb;
    object->ins = nullptr;
  }

  return (PyObject *)object;
}

