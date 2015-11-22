/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <TritonPyObject.h>
#include <xPyFunc.h>

/*
 * Class Bitvector
 *
 * - high (integer)
 * - low (integer)
 * - vectorSize (integer)
 */


void Bitvector_dealloc(PyObject *self) {
  Py_DECREF(self);
}


static char Bitvector_getHigh_doc[] = "Returns the high bit";
static PyObject *Bitvector_getHigh(PyObject *self, PyObject *noarg) {
  return Py_BuildValue("k", PyBitvector_AsHigh(self));
}


static char Bitvector_getLow_doc[] = "Returns the low bit";
static PyObject *Bitvector_getLow(PyObject *self, PyObject *noarg) {
  return Py_BuildValue("k", PyBitvector_AsLow(self));
}


static char Bitvector_getVectorSize_doc[] = "Returns the size of the bitvector";
static PyObject *Bitvector_getVectorSize(PyObject *self, PyObject *noarg) {
  uint32 vectorSize = ((PyBitvector_AsHigh(self) - PyBitvector_AsLow(self)) + 1);
  return Py_BuildValue("k", vectorSize);
}


PyMethodDef Bitvector_callbacks[] = {
  {"getHigh",       Bitvector_getHigh,        METH_NOARGS,     Bitvector_getHigh_doc},
  {"getLow",        Bitvector_getLow,         METH_NOARGS,     Bitvector_getLow_doc},
  {"getVectorSize", Bitvector_getVectorSize,  METH_NOARGS,     Bitvector_getVectorSize_doc},
  {nullptr,         nullptr,                  0,               nullptr}
};


PyTypeObject Bitvector_Type = {
    PyObject_HEAD_INIT(&PyType_Type)
    0,                                          /* ob_size*/
    "Bitvector",                                /* tp_name*/
    sizeof(Bitvector_Object),                   /* tp_basicsize*/
    0,                                          /* tp_itemsize*/
    (destructor)Bitvector_dealloc,              /* tp_dealloc*/
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
    "Bitvector objects",                        /* tp_doc */
    0,                                          /* tp_traverse */
    0,                                          /* tp_clear */
    0,                                          /* tp_richcompare */
    0,                                          /* tp_weaklistoffset */
    0,                                          /* tp_iter */
    0,                                          /* tp_iternext */
    Bitvector_callbacks,                        /* tp_methods */
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


PyObject *PyBitvector(RegisterOperand *reg) {
  Bitvector_Object *object;

  PyType_Ready(&Bitvector_Type);
  object = PyObject_NEW(Bitvector_Object, &Bitvector_Type);
  if (object != NULL) {
    object->high = reg->getHigh();
    object->low  = reg->getLow();
  }

  return (PyObject *)object;
}


PyObject *PyBitvector(MemoryOperand *mem) {
  Bitvector_Object *object;

  PyType_Ready(&Bitvector_Type);
  object = PyObject_NEW(Bitvector_Object, &Bitvector_Type);
  if (object != NULL) {
    object->high = mem->getHigh();
    object->low  = mem->getLow();
  }

  return (PyObject *)object;
}

