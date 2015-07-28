/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <TritonPyObject.h>
#include <xPyFunc.h>

/*
 * Class Operand
 *
 * - baseReg (IDREF.REG)
 * - displacement (integer)
 * - indexReg (IDREF.REG)
 * - memoryScale (integer)
 * - size (integer)
 * - type (IDREF.OPERAND)
 * - value (intger or IDREF.REG)
 */


void Operand_dealloc(PyObject *self) {
  Py_DECREF(self);
}


static char Operand_getBaseReg_doc[] = "Returns the base register";
static PyObject *Operand_getBaseReg(PyObject *self, PyObject *noarg)
{
  return Py_BuildValue("k", PyOperand_AsOperand(self)->getBaseReg());
}


static char Operand_getDisplacement_doc[] = "Returns the displacement";
static PyObject *Operand_getDisplacement(PyObject *self, PyObject *noarg)
{
  return Py_BuildValue("k", PyOperand_AsOperand(self)->getDisplacement());
}


static char Operand_getIndexReg_doc[] = "Returns the index register";
static PyObject *Operand_getIndexReg(PyObject *self, PyObject *noarg)
{
  return Py_BuildValue("k", PyOperand_AsOperand(self)->getIndexReg());
}


static char Operand_getMemoryScale_doc[] = "Returns the memory scale";
static PyObject *Operand_getMemoryScale(PyObject *self, PyObject *noarg)
{
  return Py_BuildValue("k", PyOperand_AsOperand(self)->getMemoryScale());
}


static char Operand_getSize_doc[] = "Returns the size";
static PyObject *Operand_getSize(PyObject *self, PyObject *noarg)
{
  return Py_BuildValue("k", PyOperand_AsOperand(self)->getSize());
}


static char Operand_getType_doc[] = "Returns the type";
static PyObject *Operand_getType(PyObject *self, PyObject *noarg)
{
  return Py_BuildValue("k", PyOperand_AsOperand(self)->getType());
}


static char Operand_getValue_doc[] = "Returns the value";
static PyObject *Operand_getValue(PyObject *self, PyObject *noarg)
{
  return Py_BuildValue("k", PyOperand_AsOperand(self)->getValue());
}


PyMethodDef Operand_callbacks[] = {
  {"getBaseReg",        Operand_getBaseReg,       METH_NOARGS,     Operand_getBaseReg_doc},
  {"getDisplacement",   Operand_getDisplacement,  METH_NOARGS,     Operand_getDisplacement_doc},
  {"getIndexReg",       Operand_getIndexReg,      METH_NOARGS,     Operand_getIndexReg_doc},
  {"getMemoryScale",    Operand_getMemoryScale,   METH_NOARGS,     Operand_getMemoryScale_doc},
  {"getSize",           Operand_getSize,          METH_NOARGS,     Operand_getSize_doc},
  {"getType",           Operand_getType,          METH_NOARGS,     Operand_getType_doc},
  {"getValue",          Operand_getValue,         METH_NOARGS,     Operand_getValue_doc},
  {nullptr,             nullptr,                  0,               nullptr}
};


PyTypeObject Operand_Type = {
    PyObject_HEAD_INIT(&PyType_Type)
    0,                                          /* ob_size*/
    "Operand",                                  /* tp_name*/
    sizeof(Operand_Object),                     /* tp_basicsize*/
    0,                                          /* tp_itemsize*/
    (destructor)Operand_dealloc,                /* tp_dealloc*/
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
    0,                                          /* tp_str*/
    0,                                          /* tp_getattro*/
    0,                                          /* tp_setattro*/
    0,                                          /* tp_as_buffer*/
    Py_TPFLAGS_DEFAULT,                         /* tp_flags*/
    "Operand objects",                          /* tp_doc */
    0,                                          /* tp_traverse */
    0,                                          /* tp_clear */
    0,                                          /* tp_richcompare */
    0,                                          /* tp_weaklistoffset */
    0,                                          /* tp_iter */
    0,                                          /* tp_iternext */
    Operand_callbacks,                          /* tp_methods */
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


PyObject *PyOperand(TritonOperand operand)
{
  Operand_Object *object;

  PyType_Ready(&Operand_Type);
  object = PyObject_NEW(Operand_Object, &Operand_Type);
  if (object != NULL)
    object->operand = operand;

  return (PyObject *)object;
}

