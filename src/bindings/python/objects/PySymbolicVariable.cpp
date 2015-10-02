/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <PythonUtils.h>
#include <TritonPyObject.h>
#include <xPyFunc.h>

/*
 * Class SymbolicVariable:
 *
 * - getComment() : Returns the symbolic variable comment
 * - getConcreteValue() : Returns the variable's symbolic value
 * - getId() : Returns the symbolic variable id
 * - getKind() : Returns the kind of the symbolic variable
 * - getKindValue() : Returns the kind value (IDREG.REG or integer, it depends of the kind)
 * - getName() : Returns the name of the symbolic variable
 * - getSize() : Returns the symbolic variable size
 * - hasConcreteValue() : Returns true of false if the variable contains a concrete value
 */


void SymbolicVariable_dealloc(PyObject *self) {
  Py_DECREF(self);
}


static char SymbolicVariable_getComment_doc[] = "Returns the comment of the symbolic variable";
static PyObject *SymbolicVariable_getComment(PyObject *self, PyObject *noarg) {
  SymbolicVariable *variable = PySymbolicVariable_AsSymbolicVariable(self);
  if (variable->getSymVarComment().empty() == false)
    return PyString_FromFormat("%s", variable->getSymVarComment().c_str());
  Py_INCREF(Py_None);
  return Py_None;
}

static char SymbolicVariable_getConcreteValue_doc[] = "Returns the variable's concrete value";
static PyObject *SymbolicVariable_getConcreteValue(PyObject *self, PyObject *noarg) {
  SymbolicVariable *symVar = PySymbolicVariable_AsSymbolicVariable(self);
  return uint128ToPyLongObject(symVar->getConcreteValue());
}


static char SymbolicVariable_getId_doc[] = "Returns the id of the symbolic variable";
static PyObject *SymbolicVariable_getId(PyObject *self, PyObject *noarg) {
  SymbolicVariable *variable = PySymbolicVariable_AsSymbolicVariable(self);
  return Py_BuildValue("k", variable->getSymVarId());
}


static char SymbolicVariable_getKind_doc[] = "Returns the kind of the symbolic variable";
static PyObject *SymbolicVariable_getKind(PyObject *self, PyObject *noarg) {
  SymbolicVariable *variable = PySymbolicVariable_AsSymbolicVariable(self);
  return Py_BuildValue("k", variable->getSymVarKind());
}


static char SymbolicVariable_getKindValue_doc[] = "Returns the kind value of the symbolic variable";
static PyObject *SymbolicVariable_getKindValue(PyObject *self, PyObject *noarg) {
  SymbolicVariable *variable = PySymbolicVariable_AsSymbolicVariable(self);
  return Py_BuildValue("k", variable->getSymVarKindValue());
}


static char SymbolicVariable_getName_doc[] = "Returns the name of the symbolic variable";
static PyObject *SymbolicVariable_getName(PyObject *self, PyObject *noarg) {
  SymbolicVariable *variable = PySymbolicVariable_AsSymbolicVariable(self);
  return PyString_FromFormat("%s", variable->getSymVarName().c_str());
}


static char SymbolicVariable_getSize_doc[] = "Returns the size of the symbolic variable";
static PyObject *SymbolicVariable_getSize(PyObject *self, PyObject *noarg) {
  SymbolicVariable *variable = PySymbolicVariable_AsSymbolicVariable(self);
  return Py_BuildValue("k", variable->getSymVarSize());
}


static char SymbolicVariable_hasConcreteValue_doc[] = "Returns true of false if the variable contains a concrete value";
static PyObject *SymbolicVariable_hasConcreteValue(PyObject *self, PyObject *noarg) {
  SymbolicVariable *variable = PySymbolicVariable_AsSymbolicVariable(self);
  if (variable->hasConcreteValue() == true)
    Py_RETURN_TRUE;
  Py_RETURN_FALSE;
}


static PyObject *SymbolicVariable_str(SymbolicVariable_Object *obj) {
  std::stringstream str;
  str << obj->variable->getSymVarName();
  return PyString_FromFormat("%s", str.str().c_str());
}


PyMethodDef SymbolicVariable_callbacks[] = {
  {"getComment",          SymbolicVariable_getComment,          METH_NOARGS,   SymbolicVariable_getComment_doc},
  {"getConcreteValue",    SymbolicVariable_getConcreteValue,    METH_NOARGS,   SymbolicVariable_getConcreteValue_doc},
  {"getId",               SymbolicVariable_getId,               METH_NOARGS,   SymbolicVariable_getId_doc},
  {"getKind",             SymbolicVariable_getKind,             METH_NOARGS,   SymbolicVariable_getKind_doc},
  {"getKindValue",        SymbolicVariable_getKindValue,        METH_NOARGS,   SymbolicVariable_getKindValue_doc},
  {"getName",             SymbolicVariable_getName,             METH_NOARGS,   SymbolicVariable_getName_doc},
  {"getSize",             SymbolicVariable_getSize,             METH_NOARGS,   SymbolicVariable_getSize_doc},
  {"hasConcreteValue",    SymbolicVariable_hasConcreteValue,    METH_NOARGS,   SymbolicVariable_hasConcreteValue_doc},
  {nullptr,               nullptr,                              0,             nullptr}
};


PyTypeObject SymbolicVariable_Type = {
    PyObject_HEAD_INIT(&PyType_Type)
    0,                                          /* ob_size*/
    "SymbolicVariable",                         /* tp_name*/
    sizeof(SymbolicVariable_Object),            /* tp_basicsize*/
    0,                                          /* tp_itemsize*/
    (destructor)SymbolicVariable_dealloc,       /* tp_dealloc*/
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
    (reprfunc)SymbolicVariable_str,             /* tp_str*/
    0,                                          /* tp_getattro*/
    0,                                          /* tp_setattro*/
    0,                                          /* tp_as_buffer*/
    Py_TPFLAGS_DEFAULT,                         /* tp_flags*/
    "SymbolicVariable objects",                 /* tp_doc */
    0,                                          /* tp_traverse */
    0,                                          /* tp_clear */
    0,                                          /* tp_richcompare */
    0,                                          /* tp_weaklistoffset */
    0,                                          /* tp_iter */
    0,                                          /* tp_iternext */
    SymbolicVariable_callbacks,                 /* tp_methods */
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


PyObject *PySymbolicVariable(SymbolicVariable *variable) {
  SymbolicVariable_Object *object;

  PyType_Ready(&SymbolicVariable_Type);
  object = PyObject_NEW(SymbolicVariable_Object, &SymbolicVariable_Type);
  if (object != NULL)
    object->variable = variable;

  return (PyObject *)object;
}

#endif /* LIGHT_VERSION */

