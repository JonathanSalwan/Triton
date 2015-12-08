/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <SMT2Lib.h>
#include <TritonPyObject.h>
#include <xPyFunc.h>

/*
 * Class SymbolicExpression:
 *
 * - getAst() : Returns the AST node of the expression
 * - getComment() : Returns the comment of the expression
 * - getId() : Returns the id of the expression
 * - getKind() : Returns the kind of the expression
 * - getNewAst() : Returns a duplicated AST node of the expression
 * - isMem() : Returns true if the expression is assigned to a memory
 * - isReg() : Returns true if the expression is assigned to a register
 * - isTainted() : Returns true if the expression is tainted
 */


void SymbolicExpression_dealloc(PyObject *self) {
  Py_DECREF(self);
}


static char SymbolicExpression_getAst_doc[] = "Returns the AST of the expression";
static PyObject *SymbolicExpression_getAst(PyObject *self, PyObject *noarg) {
  SymbolicExpression *expression = PySymbolicExpression_AsSymbolicExpression(self);
  return PySmtAstNode(expression->getExpression());
}


static char SymbolicExpression_getComment_doc[] = "Returns the comment of the expression";
static PyObject *SymbolicExpression_getComment(PyObject *self, PyObject *noarg) {
  SymbolicExpression *expression = PySymbolicExpression_AsSymbolicExpression(self);
  if (expression->getComment().empty() == false)
    return PyString_FromFormat("%s", expression->getComment().c_str());
  Py_INCREF(Py_None);
  return Py_None;
}


static char SymbolicExpression_getId_doc[] = "Returns the id of the expression";
static PyObject *SymbolicExpression_getId(PyObject *self, PyObject *noarg) {
  SymbolicExpression *expression = PySymbolicExpression_AsSymbolicExpression(self);
  return Py_BuildValue("k", expression->getID());
}


static char SymbolicExpression_getKind_doc[] = "Returns the kind of the expression";
static PyObject *SymbolicExpression_getKind(PyObject *self, PyObject *noarg) {
  SymbolicExpression *expression = PySymbolicExpression_AsSymbolicExpression(self);
  return Py_BuildValue("k", expression->getKind());
}


static char SymbolicExpression_getNewAst_doc[] = "Returns a duplicated AST node of the expression";
static PyObject *SymbolicExpression_getNewAst(PyObject *self, PyObject *noarg) {
  SymbolicExpression *expression = PySymbolicExpression_AsSymbolicExpression(self);
  return PySmtAstNode(smt2lib::newInstance(expression->getExpression()));
}


static char SymbolicExpression_isReg_doc[] = "Returns true if the orgin's expression is a register";
static PyObject *SymbolicExpression_isReg(PyObject *self, PyObject *noarg) {
  SymbolicExpression *expression = PySymbolicExpression_AsSymbolicExpression(self);
  if (expression->isReg() == true)
    Py_RETURN_TRUE;
  Py_RETURN_FALSE;
}


static char SymbolicExpression_isMem_doc[] = "Returns true if the orgin's expression is a memory";
static PyObject *SymbolicExpression_isMem(PyObject *self, PyObject *noarg) {
  SymbolicExpression *expression = PySymbolicExpression_AsSymbolicExpression(self);
  if (expression->isMem() == true)
    Py_RETURN_TRUE;
  Py_RETURN_FALSE;
}


static char SymbolicExpression_isTainted_doc[] = "Returns true if the expression is tainted";
static PyObject *SymbolicExpression_isTainted(PyObject *self, PyObject *noarg) {
  SymbolicExpression *expression = PySymbolicExpression_AsSymbolicExpression(self);
  if (expression->isTainted == true)
    Py_RETURN_TRUE;
  Py_RETURN_FALSE;
}


static char SymbolicExpression_setAst_doc[] = "Set a new AST of the expression";
static PyObject *SymbolicExpression_setAst(PyObject *self, PyObject *node) {
  smt2lib::smtAstAbstractNode *src;

  if (!PySmtAstNode_Check(node))
    return PyErr_Format(PyExc_TypeError, "setAst(): expected a SmtAstNode as argument");

  src = PySmtAstNode_AsSmtAstNode(node);
  PySymbolicExpression_AsSymbolicExpression(self)->setExpression(src);
  Py_RETURN_TRUE;
}



static PyObject *SymbolicExpression_str(SymbolicExpression_Object *obj) {
  std::stringstream str;
  str << "#" << obj->expression->getID() << " = " << obj->expression->getExpression();
  return PyString_FromFormat("%s", str.str().c_str());
}


PyMethodDef SymbolicExpression_callbacks[] = {
  {"getAst",      SymbolicExpression_getAst,      METH_NOARGS,   SymbolicExpression_getAst_doc},
  {"getComment",  SymbolicExpression_getComment,  METH_NOARGS,   SymbolicExpression_getComment_doc},
  {"getId",       SymbolicExpression_getId,       METH_NOARGS,   SymbolicExpression_getId_doc},
  {"getKind",     SymbolicExpression_getKind,     METH_NOARGS,   SymbolicExpression_getKind_doc},
  {"getNewAst",   SymbolicExpression_getNewAst,   METH_NOARGS,   SymbolicExpression_getNewAst_doc},
  {"isMem",       SymbolicExpression_isMem,       METH_NOARGS,   SymbolicExpression_isMem_doc},
  {"isReg",       SymbolicExpression_isReg,       METH_NOARGS,   SymbolicExpression_isReg_doc},
  {"isTainted",   SymbolicExpression_isTainted,   METH_NOARGS,   SymbolicExpression_isTainted_doc},
  {"setAst",      SymbolicExpression_setAst,      METH_O,        SymbolicExpression_setAst_doc},
  {nullptr,       nullptr,                        0,             nullptr}
};


PyTypeObject SymbolicExpression_Type = {
    PyObject_HEAD_INIT(&PyType_Type)
    0,                                          /* ob_size*/
    "SymbolicExpression",                       /* tp_name*/
    sizeof(SymbolicExpression_Object),          /* tp_basicsize*/
    0,                                          /* tp_itemsize*/
    (destructor)SymbolicExpression_dealloc,     /* tp_dealloc*/
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
    (reprfunc)SymbolicExpression_str,           /* tp_str*/
    0,                                          /* tp_getattro*/
    0,                                          /* tp_setattro*/
    0,                                          /* tp_as_buffer*/
    Py_TPFLAGS_DEFAULT,                         /* tp_flags*/
    "SymbolicExpression objects",               /* tp_doc */
    0,                                          /* tp_traverse */
    0,                                          /* tp_clear */
    0,                                          /* tp_richcompare */
    0,                                          /* tp_weaklistoffset */
    0,                                          /* tp_iter */
    0,                                          /* tp_iternext */
    SymbolicExpression_callbacks,               /* tp_methods */
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


PyObject *PySymbolicExpression(SymbolicExpression *expr) {
  SymbolicExpression_Object *object;

  PyType_Ready(&SymbolicExpression_Type);
  object = PyObject_NEW(SymbolicExpression_Object, &SymbolicExpression_Type);
  if (object != NULL)
    object->expression = expr;

  return (PyObject *)object;
}

#endif /* LIGHT_VERSION */

