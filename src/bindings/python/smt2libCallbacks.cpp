
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


static char smt2lib_bvadd_doc[] = "Returns an 'bvadd' expression";
static PyObject *smt2lib_bvadd(PyObject *self, PyObject *args)
{
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PyString_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvadd(): expected a string as first argument");

  if (op2 == nullptr || !PyString_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvadd(): expected a string as second argument");

  return Py_BuildValue("s", smt2lib::bvadd(PyString_AsString(op1), PyString_AsString(op2)).c_str());
}


static char smt2lib_bvand_doc[] = "Returns an 'bvand' expression";
static PyObject *smt2lib_bvand(PyObject *self, PyObject *args)
{
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PyString_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvand(): expected a string as first argument");

  if (op2 == nullptr || !PyString_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvand(): expected a string as second argument");

  return Py_BuildValue("s", smt2lib::bvand(PyString_AsString(op1), PyString_AsString(op2)).c_str());
}


static char smt2lib_bvfalse_doc[] = "Returns an alias on '(_ bv0 1)' expression";
static PyObject *smt2lib_bvfalse(PyObject *self, PyObject *args)
{
  return Py_BuildValue("s", smt2lib::bvfalse().c_str());
}


static char smt2lib_bvnot_doc[] = "Returns an 'bvnot' expression";
static PyObject *smt2lib_bvnot(PyObject *self, PyObject *op1)
{
  if (!PyString_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvnot(): expected a string as first argument");

  return Py_BuildValue("s", smt2lib::bvnot(PyString_AsString(op1)).c_str());
}


static char smt2lib_bvsub_doc[] = "Returns an 'bvsub' expression";
static PyObject *smt2lib_bvsub(PyObject *self, PyObject *args)
{
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PyString_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvsub(): expected a string as first argument");

  if (op2 == nullptr || !PyString_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvsub(): expected a string as second argument");

  return Py_BuildValue("s", smt2lib::bvsub(PyString_AsString(op1), PyString_AsString(op2)).c_str());
}


static char smt2lib_bvtrue_doc[] = "Returns an alias on '(_ bv1 1)' expression";
static PyObject *smt2lib_bvtrue(PyObject *self, PyObject *args)
{
  return Py_BuildValue("s", smt2lib::bvtrue().c_str());
}


static char smt2lib_bvult_doc[] = "Returns an 'bvult' expression";
static PyObject *smt2lib_bvult(PyObject *self, PyObject *args)
{
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PyString_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvult(): expected a string as first argument");

  if (op2 == nullptr || !PyString_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvult(): expected a string as second argument");

  return Py_BuildValue("s", smt2lib::bvult(PyString_AsString(op1), PyString_AsString(op2)).c_str());
}


static char smt2lib_bvxor_doc[] = "Returns an 'bvxor' expression";
static PyObject *smt2lib_bvxor(PyObject *self, PyObject *args)
{
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PyString_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvxor(): expected a string as first argument");

  if (op2 == nullptr || !PyString_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvxor(): expected a string as second argument");

  return Py_BuildValue("s", smt2lib::bvxor(PyString_AsString(op1), PyString_AsString(op2)).c_str());
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


static char smt2lib_extract_doc[] = "Returns an 'extract' expression";
static PyObject *smt2lib_extract(PyObject *self, PyObject *args)
{
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;
  PyObject *op3 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "|OOO", &op1, &op2, &op3);

  if (op1 == nullptr && op2 == nullptr && op3 == nullptr)
    return PyErr_Format(PyExc_TypeError, "extract(): expected at least one integer as first argument");

  else if ((PyLong_Check(op1) || PyInt_Check(op1)) && op2 == nullptr && op3 == nullptr)
    return Py_BuildValue("s", smt2lib::extract(PyLong_AsLong(op1)).c_str());

  else if ((PyLong_Check(op1) || PyInt_Check(op1)) && op2 != nullptr && PyString_Check(op2) && op3 == nullptr)
    return Py_BuildValue("s", smt2lib::extract(PyLong_AsLong(op1), PyString_AsString(op2)).c_str());

  else if ((PyLong_Check(op1) || PyInt_Check(op1)) && (PyLong_Check(op2) || PyInt_Check(op2)) && op3 == nullptr)
    return Py_BuildValue("s", smt2lib::extract(PyLong_AsLong(op1), PyLong_AsLong(op2)).c_str());

  else if ((PyLong_Check(op1) || PyInt_Check(op1)) && (PyLong_Check(op2) || PyInt_Check(op2)) && op3 != nullptr && PyString_Check(op3))
    return Py_BuildValue("s", smt2lib::extract(PyLong_AsLong(op1), PyLong_AsLong(op2), PyString_AsString(op3)).c_str());

  return PyErr_Format(PyExc_TypeError, "extract(): bad argument");;
}


static char smt2lib_ite_doc[] = "Returns an 'ite' expression";
static PyObject *smt2lib_ite(PyObject *self, PyObject *args)
{
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;
  PyObject *op3 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O|O", &op1, &op2, &op3);

  if (op1 == nullptr || !PyString_Check(op1))
    return PyErr_Format(PyExc_TypeError, "ite(): expected a string as first argument");

  if (op2 == nullptr || !PyString_Check(op2))
    return PyErr_Format(PyExc_TypeError, "ite(): expected a string as second argument");

  if (op3 == nullptr || !PyString_Check(op3))
    return PyErr_Format(PyExc_TypeError, "ite(): expected a string as third argument");

  return Py_BuildValue("s", smt2lib::ite(PyString_AsString(op1), PyString_AsString(op2), PyString_AsString(op3)).c_str());
}


static char smt2lib_assert_doc[] = "Returns an 'assert' expression";
static PyObject *smt2lib_assert(PyObject *self, PyObject *expr)
{
  if (!PyString_Check(expr))
    return PyErr_Format(PyExc_TypeError, "smtAssert(): expected a string as first argument");

  return Py_BuildValue("s", smt2lib::smtAssert(PyString_AsString(expr)).c_str());
}


static char smt2lib_sx_doc[] = "Returns an 'sx' expression";
static PyObject *smt2lib_sx(PyObject *self, PyObject *args)
{
  PyObject *op1 = nullptr;
  PyObject *op2;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PyString_Check(op1))
    return PyErr_Format(PyExc_TypeError, "sx(): expected a string as first argument");

  if (!PyLong_Check(op2) && !PyInt_Check(op2))
    return PyErr_Format(PyExc_TypeError, "sx(): expected an integer as second argument");

  return Py_BuildValue("s", smt2lib::sx(PyString_AsString(op1), PyLong_AsLong(op2)).c_str());
}


static char smt2lib_zx_doc[] = "Returns an 'zx' expression";
static PyObject *smt2lib_zx(PyObject *self, PyObject *args)
{
  PyObject *op1 = nullptr;
  PyObject *op2;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PyString_Check(op1))
    return PyErr_Format(PyExc_TypeError, "zx(): expected a string as first argument");

  if (!PyLong_Check(op2) && !PyInt_Check(op2))
    return PyErr_Format(PyExc_TypeError, "zx(): expected an integer as second argument");

  return Py_BuildValue("s", smt2lib::zx(PyString_AsString(op1), PyLong_AsLong(op2)).c_str());
}


PyMethodDef smt2libCallbacks[] = {
  {"bv",          smt2lib_bv,         METH_VARARGS,     smt2lib_bv_doc},
  {"bvadd",       smt2lib_bvadd,      METH_VARARGS,     smt2lib_bvadd_doc},
  {"bvand",       smt2lib_bvand,      METH_VARARGS,     smt2lib_bvand_doc},
  {"bvfalse",     smt2lib_bvfalse,    METH_NOARGS,      smt2lib_bvfalse_doc},
  {"bvnot",       smt2lib_bvnot,      METH_O,           smt2lib_bvnot_doc},
  {"bvsub",       smt2lib_bvsub,      METH_VARARGS,     smt2lib_bvsub_doc},
  {"bvtrue",      smt2lib_bvtrue,     METH_NOARGS,      smt2lib_bvtrue_doc},
  {"bvult",       smt2lib_bvult,      METH_VARARGS,     smt2lib_bvult_doc},
  {"bvxor",       smt2lib_bvxor,      METH_VARARGS,     smt2lib_bvxor_doc},
  {"equal",       smt2lib_equal,      METH_VARARGS,     smt2lib_equal_doc},
  {"extract",     smt2lib_extract,    METH_VARARGS,     smt2lib_extract_doc},
  {"ite",         smt2lib_ite,        METH_VARARGS,     smt2lib_ite_doc},
  {"smtAssert",   smt2lib_assert,     METH_O,           smt2lib_assert_doc},
  {"sx",          smt2lib_sx,         METH_VARARGS,     smt2lib_sx_doc},
  {"zx",          smt2lib_zx,         METH_VARARGS,     smt2lib_zx_doc},
  {nullptr,       nullptr,            0,                nullptr}
};

