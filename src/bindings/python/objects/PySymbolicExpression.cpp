/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <TritonPyObject.h>
#include <xPyFunc.h>

/*
 * Class SymbolicExpression:
 *
 * - getAst() : Returns the AST node of the expression
 * - getComment() : Returns the comment of the expression
 * - getId() : Returns the id of the expression
 * - isTainted (): Returns true of false if the expression is tainted
 */


void SymbolicExpression_dealloc(PyObject *self) {
  Py_DECREF(self);
}


static char SymbolicExpression_getAst_doc[] = "Returns the AST of the expression";
static PyObject *SymbolicExpression_getAst(PyObject *self, PyObject *noarg)
{
  SymbolicExpression *expression = PySymbolicExpression_AsSymbolicExpression(self);
  return PySmtAstNode(expression->getExpression());
}


static char SymbolicExpression_getComment_doc[] = "Returns the comment of the expression";
static PyObject *SymbolicExpression_getComment(PyObject *self, PyObject *noarg)
{
  SymbolicExpression *expression = PySymbolicExpression_AsSymbolicExpression(self);
  if (expression->getComment().empty() == false)
    return PyString_FromFormat("%s", expression->getComment().c_str());
  Py_INCREF(Py_None);
  return Py_None;
}


static char SymbolicExpression_getId_doc[] = "Returns the id of the expression";
static PyObject *SymbolicExpression_getId(PyObject *self, PyObject *noarg)
{
  SymbolicExpression *expression = PySymbolicExpression_AsSymbolicExpression(self);
  return Py_BuildValue("k", expression->getID());
}



static char SymbolicExpression_isTainted_doc[] = "Returns true if the expression is tainted";
static PyObject *SymbolicExpression_isTainted(PyObject *self, PyObject *noarg)
{
  SymbolicExpression *expression = PySymbolicExpression_AsSymbolicExpression(self);
  if (expression->isTainted == true)
    Py_RETURN_TRUE;
  Py_RETURN_FALSE;
}


static PyObject *SymbolicExpression_str(SymbolicExpression_Object *obj)
{
  std::stringstream str;
  str << "#" << obj->expression->getID() << " = " << obj->expression->getExpression();
  return PyString_FromFormat("%s", str.str().c_str());
}


PyMethodDef SymbolicExpression_callbacks[] = {
  {"getAst",      SymbolicExpression_getAst,      METH_NOARGS,   SymbolicExpression_getAst_doc},
  {"getComment",  SymbolicExpression_getComment,  METH_NOARGS,   SymbolicExpression_getComment_doc},
  {"getId",       SymbolicExpression_getId,       METH_NOARGS,   SymbolicExpression_getId_doc},
  {"isTainted",   SymbolicExpression_isTainted,   METH_NOARGS,   SymbolicExpression_isTainted_doc},
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


PyObject *PySymbolicExpression(SymbolicExpression *expr)
{
  SymbolicExpression_Object *object;

  PyType_Ready(&SymbolicExpression_Type);
  object = PyObject_NEW(SymbolicExpression_Object, &SymbolicExpression_Type);
  if (object != NULL)
    object->expression = expr;

  return (PyObject *)object;
}

