
#include <python2.7/Python.h>

#include "SMT2Lib.h"


static char smt2lib_bv_doc[] = "Returns a 'bv' expression";
static PyObject *smt2lib_bv(PyObject *self, PyObject *args)
{
  PyObject *op1;
  PyObject *op2;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (!PyLong_Check(op1) && !PyInt_Check(op1))
      return PyErr_Format(PyExc_TypeError, "bv(): expected an integer as first argument");

  if (!PyLong_Check(op2) && !PyInt_Check(op2))
      return PyErr_Format(PyExc_TypeError, "bv(): expected an integer as second argument");

  return Py_BuildValue("s", smt2lib::bv(PyLong_AsLong(op1), PyLong_AsLong(op2)).c_str());
}


static char smt2lib_equal_doc[] = "Returns an 'equal' expression";
static PyObject *smt2lib_equal(PyObject *self, PyObject *args)
{
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PyString_Check(op1))
      return PyErr_Format(PyExc_TypeError, "equal(): expected a string as first argument");

  if (op2 == nullptr || !PyString_Check(op2))
      return PyErr_Format(PyExc_TypeError, "equal(): expected a string as second argument");

  return Py_BuildValue("s", smt2lib::equal(PyString_AsString(op1), PyString_AsString(op2)).c_str());
}


static char smt2lib_assert_doc[] = "Returns an 'assert' expression";
static PyObject *smt2lib_assert(PyObject *self, PyObject *expr)
{
  if (!PyString_Check(expr))
      return PyErr_Format(PyExc_TypeError, "smtAssert(): expected a string as first argument");

  return Py_BuildValue("s", smt2lib::smtAssert(PyString_AsString(expr)).c_str());
}


PyMethodDef smt2libCallbacks[] = {
  {"bv",          smt2lib_bv,         METH_VARARGS,     smt2lib_bv_doc},
  {"equal",       smt2lib_equal,      METH_VARARGS,     smt2lib_equal_doc},
  {"smtAssert",   smt2lib_assert,     METH_O,           smt2lib_assert_doc},
  {nullptr,       nullptr,            0,                nullptr}
};

