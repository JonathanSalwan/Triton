/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <TritonPyObject.h>
#include <xPyFunc.h>

/*
 * Class MemoryOperand
 *
 * - address (integer)
 * - size (integer)
 */


void MemoryOperand_dealloc(PyObject *self) {
  delete PyMemoryOperand_AsMemoryOperand(self);
  Py_DECREF(self);
}


static char MemoryOperand_getAddress_doc[] = "Returns the memory address";
static PyObject *MemoryOperand_getAddress(PyObject *self, PyObject *noarg) {
  return Py_BuildValue("k", PyMemoryOperand_AsMemoryOperand(self)->getAddress());
}


static char MemoryOperand_getSize_doc[] = "Returns the memory size";
static PyObject *MemoryOperand_getSize(PyObject *self, PyObject *noarg) {
  return Py_BuildValue("k", PyMemoryOperand_AsMemoryOperand(self)->getSize());
}


PyMethodDef MemoryOperand_callbacks[] = {
  {"getAddress",    MemoryOperand_getAddress,   METH_NOARGS,     MemoryOperand_getAddress_doc},
  {"getSize",       MemoryOperand_getSize,      METH_NOARGS,     MemoryOperand_getSize_doc},
  {nullptr,         nullptr,                    0,               nullptr}
};


PyTypeObject MemoryOperand_Type = {
    PyObject_HEAD_INIT(&PyType_Type)
    0,                                          /* ob_size*/
    "MemoryOperand",                            /* tp_name*/
    sizeof(MemoryOperand_Object),               /* tp_basicsize*/
    0,                                          /* tp_itemsize*/
    (destructor)MemoryOperand_dealloc,          /* tp_dealloc*/
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
    "MemoryOperand objects",                    /* tp_doc */
    0,                                          /* tp_traverse */
    0,                                          /* tp_clear */
    0,                                          /* tp_richcompare */
    0,                                          /* tp_weaklistoffset */
    0,                                          /* tp_iter */
    0,                                          /* tp_iternext */
    MemoryOperand_callbacks,                    /* tp_methods */
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


PyObject *PyMemoryOperand(MemoryOperand mem) {
  MemoryOperand_Object *object;

  PyType_Ready(&MemoryOperand_Type);
  object = PyObject_NEW(MemoryOperand_Object, &MemoryOperand_Type);
  if (object != NULL)
    object->mem = new MemoryOperand(mem);

  return (PyObject *)object;
}

