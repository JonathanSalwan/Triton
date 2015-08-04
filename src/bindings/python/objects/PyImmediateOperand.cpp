/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <TritonPyObject.h>
#include <xPyFunc.h>

/*
 * Class ImmediateOperand
 *
 * - value (integer)
 */


void ImmediateOperand_dealloc(PyObject *self) {
  delete PyImmediateOperand_AsImmediateOperand(self);
  Py_DECREF(self);
}


static char ImmediateOperand_getValue_doc[] = "Returns the immediate value";
static PyObject *ImmediateOperand_getValue(PyObject *self, PyObject *noarg) {
  return Py_BuildValue("k", PyImmediateOperand_AsImmediateOperand(self)->getValue());
}


PyMethodDef ImmediateOperand_callbacks[] = {
  {"getValue",      ImmediateOperand_getValue,  METH_NOARGS,     ImmediateOperand_getValue_doc},
  {nullptr,         nullptr,                    0,               nullptr}
};


PyTypeObject ImmediateOperand_Type = {
    PyObject_HEAD_INIT(&PyType_Type)
    0,                                          /* ob_size*/
    "ImmediateOperand",                         /* tp_name*/
    sizeof(ImmediateOperand_Object),            /* tp_basicsize*/
    0,                                          /* tp_itemsize*/
    (destructor)ImmediateOperand_dealloc,       /* tp_dealloc*/
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
    "ImmediateOperand objects",                 /* tp_doc */
    0,                                          /* tp_traverse */
    0,                                          /* tp_clear */
    0,                                          /* tp_richcompare */
    0,                                          /* tp_weaklistoffset */
    0,                                          /* tp_iter */
    0,                                          /* tp_iternext */
    ImmediateOperand_callbacks,                 /* tp_methods */
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


PyObject *PyImmediateOperand(ImmediateOperand imm) {
  ImmediateOperand_Object *object;

  PyType_Ready(&ImmediateOperand_Type);
  object = PyObject_NEW(ImmediateOperand_Object, &ImmediateOperand_Type);
  if (object != NULL)
    object->imm = new ImmediateOperand(imm);

  return (PyObject *)object;
}

