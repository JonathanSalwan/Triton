/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <TritonPyObject.h>
#include <xPyFunc.h>

/*
 * Class RegisterOperand
 *
 * - id (IDREF.REG)
 * - size (integer)
 */


void RegisterOperand_dealloc(PyObject *self) {
  delete PyRegisterOperand_AsRegisterOperand(self);
  Py_DECREF(self);
}


static char RegisterOperand_getId_doc[] = "Returns the register id";
static PyObject *RegisterOperand_getId(PyObject *self, PyObject *noarg) {
  return Py_BuildValue("k", PyRegisterOperand_AsRegisterOperand(self)->getTritonRegId());
}


static char RegisterOperand_getName_doc[] = "Returns the register name";
static PyObject *RegisterOperand_getName(PyObject *self, PyObject *noarg) {
  return Py_BuildValue("s", PyRegisterOperand_AsRegisterOperand(self)->getName().c_str());
}


static char RegisterOperand_getSize_doc[] = "Returns the register size";
static PyObject *RegisterOperand_getSize(PyObject *self, PyObject *noarg) {
  return Py_BuildValue("k", PyRegisterOperand_AsRegisterOperand(self)->getSize());
}


PyMethodDef RegisterOperand_callbacks[] = {
  {"getId",         RegisterOperand_getId,    METH_NOARGS,     RegisterOperand_getId_doc},
  {"getName",       RegisterOperand_getName,  METH_NOARGS,     RegisterOperand_getName_doc},
  {"getSize",       RegisterOperand_getSize,  METH_NOARGS,     RegisterOperand_getSize_doc},
  {nullptr,         nullptr,                  0,               nullptr}
};


PyTypeObject RegisterOperand_Type = {
    PyObject_HEAD_INIT(&PyType_Type)
    0,                                          /* ob_size*/
    "RegisterOperand",                          /* tp_name*/
    sizeof(RegisterOperand_Object),             /* tp_basicsize*/
    0,                                          /* tp_itemsize*/
    (destructor)RegisterOperand_dealloc,        /* tp_dealloc*/
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
    "RegisterOperand objects",                  /* tp_doc */
    0,                                          /* tp_traverse */
    0,                                          /* tp_clear */
    0,                                          /* tp_richcompare */
    0,                                          /* tp_weaklistoffset */
    0,                                          /* tp_iter */
    0,                                          /* tp_iternext */
    RegisterOperand_callbacks,                  /* tp_methods */
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


PyObject *PyRegisterOperand(RegisterOperand reg) {
  RegisterOperand_Object *object;

  PyType_Ready(&RegisterOperand_Type);
  object = PyObject_NEW(RegisterOperand_Object, &RegisterOperand_Type);
  if (object != NULL)
    object->reg = new RegisterOperand(reg);

  return (PyObject *)object;
}

