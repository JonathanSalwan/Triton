
#include <TritonPyObject.h>
#include <xPyFunc.h>

/*
 * Class SymbolicExpression:
 *
 * - ast (SmtAstNode)
 * - comment (string)
 * - id (integer)
 * - isTainted (bool)
 */

PyObject *PySymbolicExpression(SymbolicExpression *expression)
{
  if (expression == nullptr)
    return Py_None;

  PyObject *dictSEClass = xPyDict_New();
  PyDict_SetItemString(dictSEClass, "ast",          PySmtAstNode(expression->getExpression()));

  PyObject *comment = Py_None;
  if (expression->getComment()->empty() == false)
    comment = PyString_FromFormat("%s", expression->getComment()->c_str());

  PyDict_SetItemString(dictSEClass, "comment",      comment);
  PyDict_SetItemString(dictSEClass, "id",           PyLong_FromLong(expression->getID()));
  PyDict_SetItemString(dictSEClass, "isTainted",    PyBool_FromLong(expression->isTainted));

  PyObject *SEClassName = xPyString_FromString("SymbolicExpression");
  PyObject *SEClass = xPyClass_New(nullptr, dictSEClass, SEClassName);

  Py_DECREF(dictSEClass);
  Py_DECREF(SEClassName);
  Py_INCREF(SEClass);

  return SEClass;
}

