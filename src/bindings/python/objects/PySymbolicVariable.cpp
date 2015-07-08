
#include <TritonPyObject.h>
#include <xPyFunc.h>

/*
 * Class SymbolicVariable:
 *
 * - id (integer)
 * - kind (IDREF.SYMVAR)
 * - kindValue (IDREG.REG or integer, it depends of the kind)
 * - name (string)
 * - size (integer)
 * - comment(string)
 */

PyObject *PySymbolicVariable(SymbolicVariable *symVar)
{
  if (symVar == nullptr)
    return Py_None;

  PyObject *dictSVClass = xPyDict_New();
  PyDict_SetItemString(dictSVClass, "id",        PyLong_FromLong(symVar->getSymVarId()));
  PyDict_SetItemString(dictSVClass, "kind",      PyLong_FromLong(symVar->getSymVarKind()));
  PyDict_SetItemString(dictSVClass, "kindValue", PyLong_FromLong(symVar->getSymVarKindValue()));
  PyDict_SetItemString(dictSVClass, "name",      PyString_FromFormat("%s", symVar->getSymVarName().c_str()));
  PyDict_SetItemString(dictSVClass, "size",      PyLong_FromLong(symVar->getSymVarSize()));

  PyObject *comment = Py_None;
  if (symVar->getSymVarComment().empty() == false)
    comment = PyString_FromFormat("%s", symVar->getSymVarComment().c_str());

  PyDict_SetItemString(dictSVClass, "comment", comment);

  PyObject *SVClassName = xPyString_FromString("SymbolicVariable");
  PyObject *SVClass = xPyClass_New(nullptr, dictSVClass, SVClassName);

  Py_DECREF(dictSVClass);
  Py_DECREF(SVClassName);
  Py_INCREF(SVClass);

  return SVClass;
}

