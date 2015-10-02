/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <TritonPyObject.h>
#include <xPyFunc.h>
#include <PythonUtils.h>

/*
 * Class SmtAstNode:
 *
 * - getChilds() : Returns the childs of the node
 * - getKind() : Returns the kind of the node
 * - getValue() : Returns the value of the node
 * - setChild(index, node) : Set a child at a specific index
 */


void SmtAstNode_dealloc(PyObject *self) {
  Py_DECREF(self);
}


static char SmtAstNode_getChilds_doc[] = "Returns the childs of the AST node";
static PyObject *SmtAstNode_getChilds(PyObject *self, PyObject *noarg) {
  PyObject *childs;
  smt2lib::smtAstAbstractNode *node = PySmtAstNode_AsSmtAstNode(self);

  uint64 size = node->getChilds().size();
  childs = xPyList_New(size);
  uint64 index = 0;
  for ( ; index < size; index++)
    PyList_SetItem(childs, index, PySmtAstNode(node->getChilds()[index]));

  return childs;
}


static char SmtAstNode_getKind_doc[] = "Returns the kind of the AST node";
static PyObject *SmtAstNode_getKind(PyObject *self, PyObject *noarg) {
  return Py_BuildValue("k", PySmtAstNode_AsSmtAstNode(self)->getKind());
}


static char SmtAstNode_getValue_doc[] = "Returns the value of the AST node";
static PyObject *SmtAstNode_getValue(PyObject *self, PyObject *noarg) {
  smt2lib::smtAstAbstractNode *node = PySmtAstNode_AsSmtAstNode(self);

  if (node->getKind() == smt2lib::DECIMAL_NODE)
    return uint128ToPyLongObject(reinterpret_cast<smt2lib::smtAstDecimalNode *>(node)->getValue());

  else if (node->getKind() == smt2lib::STRING_NODE)
    return Py_BuildValue("s", reinterpret_cast<smt2lib::smtAstStringNode *>(node)->getValue().c_str());

  else if (node->getKind() == smt2lib::REFERENCE_NODE)
    return Py_BuildValue("k", reinterpret_cast<smt2lib::smtAstReferenceNode *>(node)->getValue());

  return PyErr_Format(PyExc_TypeError, "SmtAstNode.getValue() - Cannot use getValue() on this kind of node");
}


static char SmtAstNode_setChild_doc[] = "Set a new child node";
static PyObject *SmtAstNode_setChild(PyObject *self, PyObject *args) {
  PyObject *index;
  PyObject *node;
  uint64 i;
  smt2lib::smtAstAbstractNode *dst, *src;

  PyArg_ParseTuple(args, "O|O", &index, &node);

  if (!PyLong_Check(index) && !PyInt_Check(index))
    return PyErr_Format(PyExc_TypeError, "setChild(): expected an index (integer) as first argument");

  if (!PySmtAstNode_Check(node))
    return PyErr_Format(PyExc_TypeError, "setChild(): expected a SmtAstNode as second argument");

  i = PyLong_AsLong(index);
  src = PySmtAstNode_AsSmtAstNode(node);
  dst = PySmtAstNode_AsSmtAstNode(self);
  if (i >= dst->getChilds().size())
    return PyErr_Format(PyExc_TypeError, "setChild(): index out-of-range");

  dst->getChilds()[i] = src;

  Py_RETURN_TRUE;
}


static PyObject *SmtAstNode_str(SmtAstNode_Object *obj) {
  std::stringstream str;
  str << obj->node;
  return PyString_FromFormat("%s", str.str().c_str());
}


PyMethodDef SmtAstNode_callbacks[] = {
  {"getChilds",   SmtAstNode_getChilds, METH_NOARGS,     SmtAstNode_getChilds_doc},
  {"getKind",     SmtAstNode_getKind,   METH_NOARGS,     SmtAstNode_getKind_doc},
  {"getValue",    SmtAstNode_getValue,  METH_NOARGS,     SmtAstNode_getValue_doc},
  {"setChild",    SmtAstNode_setChild,  METH_VARARGS,    SmtAstNode_setChild_doc},
  {nullptr,       nullptr,              0,               nullptr}
};


PyTypeObject SmtAstNode_Type = {
    PyObject_HEAD_INIT(&PyType_Type)
    0,                                          /* ob_size*/
    "SmtAstNode",                               /* tp_name*/
    sizeof(SmtAstNode_Object),                  /* tp_basicsize*/
    0,                                          /* tp_itemsize*/
    (destructor)SmtAstNode_dealloc,             /* tp_dealloc*/
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
    (reprfunc)SmtAstNode_str,                   /* tp_str*/
    0,                                          /* tp_getattro*/
    0,                                          /* tp_setattro*/
    0,                                          /* tp_as_buffer*/
    Py_TPFLAGS_DEFAULT,                         /* tp_flags*/
    "SmtAstNode objects",                       /* tp_doc */
    0,                                          /* tp_traverse */
    0,                                          /* tp_clear */
    0,                                          /* tp_richcompare */
    0,                                          /* tp_weaklistoffset */
    0,                                          /* tp_iter */
    0,                                          /* tp_iternext */
    SmtAstNode_callbacks,                       /* tp_methods */
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


PyObject *PySmtAstNode(smt2lib::smtAstAbstractNode *node) {
  SmtAstNode_Object *object;

  PyType_Ready(&SmtAstNode_Type);
  object = PyObject_NEW(SmtAstNode_Object, &SmtAstNode_Type);
  if (object != NULL)
    object->node = node;

  return (PyObject *)object;
}

#endif /* LIGHT_VERSION */

