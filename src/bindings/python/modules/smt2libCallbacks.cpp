/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <python2.7/Python.h>

#include <SMT2Lib.h>
#include <TritonPyObject.h>


static char smt2lib_bv_doc[] = "Returns a 'bv' expression";
static PyObject *smt2lib_bv(PyObject *self, PyObject *args) {
  PyObject *op1;
  PyObject *op2;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (!PyLong_Check(op1) && !PyInt_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bv(): expected an integer as first argument");

  if (!PyLong_Check(op2) && !PyInt_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bv(): expected an integer as second argument");

  return PySmtAstNode(smt2lib::bv(PyLong_AsLong(op1), PyLong_AsLong(op2)));
}


static char smt2lib_bvadd_doc[] = "Returns a 'bvadd' expression";
static PyObject *smt2lib_bvadd(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvadd(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvadd(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvadd(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvand_doc[] = "Returns a 'bvand' expression";
static PyObject *smt2lib_bvand(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvand(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvand(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvand(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvashr_doc[] = "Returns a 'bvashr' expression";
static PyObject *smt2lib_bvashr(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvashr(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvashr(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvashr(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvfalse_doc[] = "Returns an alias on '(_ bv0 1)' expression";
static PyObject *smt2lib_bvfalse(PyObject *self, PyObject *args) {
  return PySmtAstNode(smt2lib::bvfalse());
}


static char smt2lib_bvlshr_doc[] = "Returns a 'bvlshr' expression";
static PyObject *smt2lib_bvlshr(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvlshr(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvlshr(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvlshr(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvmul_doc[] = "Returns a 'bvmul' expression";
static PyObject *smt2lib_bvmul(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvmul(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvmul(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvmul(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvnand_doc[] = "Returns a 'bvnand' expression";
static PyObject *smt2lib_bvnand(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvnand(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvnand(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvnand(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvneg_doc[] = "Returns a 'bvneg' expression";
static PyObject *smt2lib_bvneg(PyObject *self, PyObject *op1) {
  if (!PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvneg(): expected a SmtAstNode as first argument");

  return PySmtAstNode(smt2lib::bvneg(PySmtAstNode_AsSmtAstNode(op1)));
}


static char smt2lib_bvnor_doc[] = "Returns a 'bvnor' expression";
static PyObject *smt2lib_bvnor(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvnor(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvnor(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvnor(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvnot_doc[] = "Returns a 'bvnot' expression";
static PyObject *smt2lib_bvnot(PyObject *self, PyObject *op1) {
  if (!PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvnot(): expected a SmtAstNode as first argument");

  return PySmtAstNode(smt2lib::bvnot(PySmtAstNode_AsSmtAstNode(op1)));
}


static char smt2lib_bvor_doc[] = "Returns a 'bvor' expression";
static PyObject *smt2lib_bvor(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvor(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvor(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvor(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvror_doc[] = "Returns a 'bvror' expression";
static PyObject *smt2lib_bvror(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (!PyLong_Check(op1) && !PyInt_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvror(): expected an integer as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvror(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvror(PyLong_AsLong(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvrol_doc[] = "Returns a 'bvrol' expression";
static PyObject *smt2lib_bvrol(PyObject *self, PyObject *args) {
  PyObject *op1;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (!PyLong_Check(op1) && !PyInt_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvrol(): expected a integer as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvrol(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvrol(PyLong_AsLong(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvsdiv_doc[] = "Returns a 'bvsdiv' expression";
static PyObject *smt2lib_bvsdiv(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvsdiv(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvsdiv(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvsdiv(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvsge_doc[] = "Returns a 'bvsge' expression";
static PyObject *smt2lib_bvsge(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvsge(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvsge(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvsge(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvsgt_doc[] = "Returns a 'bvsgt' expression";
static PyObject *smt2lib_bvsgt(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvsgt(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvsgt(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvsgt(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvshl_doc[] = "Returns a 'bvshl' expression";
static PyObject *smt2lib_bvshl(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvshl(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvshl(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvshl(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvsle_doc[] = "Returns a 'bvsle' expression";
static PyObject *smt2lib_bvsle(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvsle(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvsle(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvsle(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvslt_doc[] = "Returns a 'bvslt' expression";
static PyObject *smt2lib_bvslt(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvslt(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvslt(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvslt(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvsmod_doc[] = "Returns a 'bvsmod' expression";
static PyObject *smt2lib_bvsmod(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvsmod(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvsmod(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvsmod(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvsrem_doc[] = "Returns a 'bvsrem' expression";
static PyObject *smt2lib_bvsrem(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvsrem(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvsrem(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvsrem(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvsub_doc[] = "Returns a 'bvsub' expression";
static PyObject *smt2lib_bvsub(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvsub(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvsub(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvsub(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvtrue_doc[] = "Returns an alias on '(_ bv1 1)' expression";
static PyObject *smt2lib_bvtrue(PyObject *self, PyObject *args) {
  return PySmtAstNode(smt2lib::bvtrue());
}


static char smt2lib_bvudiv_doc[] = "Returns a 'bvudiv' expression";
static PyObject *smt2lib_bvudiv(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvudiv(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvudiv(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvudiv(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvuge_doc[] = "Returns a 'bvuge' expression";
static PyObject *smt2lib_bvuge(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvuge(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvuge(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvuge(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvugt_doc[] = "Returns a 'bvugt' expression";
static PyObject *smt2lib_bvugt(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvugt(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvugt(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvugt(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvule_doc[] = "Returns a 'bvule' expression";
static PyObject *smt2lib_bvule(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvule(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvule(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvule(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvult_doc[] = "Returns a 'bvult' expression";
static PyObject *smt2lib_bvult(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvult(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvult(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvult(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvurem_doc[] = "Returns a 'bvurem' expression";
static PyObject *smt2lib_bvurem(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvurem(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvurem(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvurem(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvxnor_doc[] = "Returns a 'bvxnor' expression";
static PyObject *smt2lib_bvxnor(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvxnor(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvxnor(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvxnor(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_bvxor_doc[] = "Returns a 'bvxor' expression";
static PyObject *smt2lib_bvxor(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "bvxor(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "bvxor(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::bvxor(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_distinct_doc[] = "Returns an 'distinct' expression";
static PyObject *smt2lib_distinct(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "distinct(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "distinct(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::distinct(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_compound_doc[] = "Returns a compound of expressions";
static PyObject *smt2lib_compound(PyObject *self, PyObject *exprsList) {
  std::vector<smt2lib::smtAstAbstractNode *> exprs;

  if (exprsList == nullptr || !PyList_Check(exprsList))
    return PyErr_Format(PyExc_TypeError, "compound(): expected a list of SmtAstNodes as first argument");

  /* Check if the mems list contains only integer item and craft a std::list */
  for (Py_ssize_t i = 0; i < PyList_Size(exprsList); i++){
    PyObject *item = PyList_GetItem(exprsList, i);

    if (!PySmtAstNode_Check(item))
      return PyErr_Format(PyExc_TypeError, "compound(): Each element from the list must be a SmtAstNode");

    exprs.push_back(PySmtAstNode_AsSmtAstNode(item));
  }

  return PySmtAstNode(smt2lib::compound(exprs));
}


static char smt2lib_equal_doc[] = "Returns an 'equal' expression";
static PyObject *smt2lib_equal(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "equal(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "equal(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::equal(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_extract_doc[] = "Returns an 'extract' expression";
static PyObject *smt2lib_extract(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;
  PyObject *op3 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O|O", &op1, &op2, &op3);

  if (!PyLong_Check(op1) && !PyInt_Check(op1))
    return PyErr_Format(PyExc_TypeError, "extract(): expected an integer as first argument");

  if (!PyLong_Check(op2) && !PyInt_Check(op2))
    return PyErr_Format(PyExc_TypeError, "extract(): expected an integer as second argument");

  if (op3 == nullptr || !PySmtAstNode_Check(op3))
    return PyErr_Format(PyExc_TypeError, "extract(): expected a SmtAstNode as third argument");

  return PySmtAstNode(smt2lib::extract(PyLong_AsLong(op1), PyLong_AsLong(op2), PySmtAstNode_AsSmtAstNode(op3)));
}


static char smt2lib_ite_doc[] = "Returns an 'ite' expression";
static PyObject *smt2lib_ite(PyObject *self, PyObject *args) {
  PyObject *op1 = nullptr;
  PyObject *op2 = nullptr;
  PyObject *op3 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O|O", &op1, &op2, &op3);

  if (op1 == nullptr || !PySmtAstNode_Check(op1))
    return PyErr_Format(PyExc_TypeError, "ite(): expected a SmtAstNode as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "ite(): expected a SmtAstNode as second argument");

  if (op3 == nullptr || !PySmtAstNode_Check(op3))
    return PyErr_Format(PyExc_TypeError, "ite(): expected a SmtAstNode as third argument");

  return PySmtAstNode(smt2lib::ite(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2), PySmtAstNode_AsSmtAstNode(op3)));
}


static char smt2lib_smtAssert_doc[] = "Returns an 'assert' expression";
static PyObject *smt2lib_smtAssert(PyObject *self, PyObject *expr) {
  if (!PySmtAstNode_Check(expr))
    return PyErr_Format(PyExc_TypeError, "smtAssert(): expected a SmtAstNode as first argument");

  return PySmtAstNode(smt2lib::smtAssert(PySmtAstNode_AsSmtAstNode(expr)));
}


static char smt2lib_string_doc[] = "Returns a 'string' node";
static PyObject *smt2lib_string(PyObject *self, PyObject *expr) {
  if (!PyString_Check(expr))
    return PyErr_Format(PyExc_TypeError, "string(): expected a string as first argument");

  return PySmtAstNode(smt2lib::string(PyString_AsString(expr)));
}


static char smt2lib_sx_doc[] = "Returns an 'sx' expression";
static PyObject *smt2lib_sx(PyObject *self, PyObject *args) {
  PyObject *op1;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (!PyLong_Check(op1) && !PyInt_Check(op1))
    return PyErr_Format(PyExc_TypeError, "sx(): expected an integer as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "sx(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::sx(PyLong_AsLong(op1), PySmtAstNode_AsSmtAstNode(op2)));
}


static char smt2lib_variable_doc[] = "Returns a 'variable' node";
static PyObject *smt2lib_variable(PyObject *self, PyObject *expr) {
  if (!PyString_Check(expr))
    return PyErr_Format(PyExc_TypeError, "string(): expected a string as first argument");

  return PySmtAstNode(smt2lib::variable(PyString_AsString(expr)));
}


static char smt2lib_zx_doc[] = "Returns an 'zx' expression";
static PyObject *smt2lib_zx(PyObject *self, PyObject *args) {
  PyObject *op1;
  PyObject *op2 = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &op1, &op2);

  if (!PyLong_Check(op1) && !PyInt_Check(op1))
    return PyErr_Format(PyExc_TypeError, "zx(): expected an integer as first argument");

  if (op2 == nullptr || !PySmtAstNode_Check(op2))
    return PyErr_Format(PyExc_TypeError, "zx(): expected a SmtAstNode as second argument");

  return PySmtAstNode(smt2lib::zx(PyLong_AsLong(op2), PySmtAstNode_AsSmtAstNode(op2)));
}


PyMethodDef smt2libCallbacks[] = {
  {"bv",          smt2lib_bv,         METH_VARARGS,     smt2lib_bv_doc},
  {"bvadd",       smt2lib_bvadd,      METH_VARARGS,     smt2lib_bvadd_doc},
  {"bvand",       smt2lib_bvand,      METH_VARARGS,     smt2lib_bvand_doc},
  {"bvashr",      smt2lib_bvashr,     METH_VARARGS,     smt2lib_bvashr_doc},
  {"bvfalse",     smt2lib_bvfalse,    METH_NOARGS,      smt2lib_bvfalse_doc},
  {"bvlshr",      smt2lib_bvlshr,     METH_VARARGS,     smt2lib_bvlshr_doc},
  {"bvmul",       smt2lib_bvmul,      METH_VARARGS,     smt2lib_bvmul_doc},
  {"bvnand",      smt2lib_bvnand,     METH_VARARGS,     smt2lib_bvnand_doc},
  {"bvneg",       smt2lib_bvneg,      METH_O,           smt2lib_bvneg_doc},
  {"bvnor",       smt2lib_bvnor,      METH_VARARGS,     smt2lib_bvnor_doc},
  {"bvnot",       smt2lib_bvnot,      METH_O,           smt2lib_bvnot_doc},
  {"bvor",        smt2lib_bvor,       METH_VARARGS,     smt2lib_bvor_doc},
  {"bvrol",       smt2lib_bvrol,      METH_VARARGS,     smt2lib_bvrol_doc},
  {"bvror",       smt2lib_bvror,      METH_VARARGS,     smt2lib_bvror_doc},
  {"bvsdiv",      smt2lib_bvsdiv,     METH_VARARGS,     smt2lib_bvsdiv_doc},
  {"bvsge",       smt2lib_bvsge,      METH_VARARGS,     smt2lib_bvsge_doc},
  {"bvsgt",       smt2lib_bvsgt,      METH_VARARGS,     smt2lib_bvsgt_doc},
  {"bvshl",       smt2lib_bvshl,      METH_VARARGS,     smt2lib_bvshl_doc},
  {"bvsle",       smt2lib_bvsle,      METH_VARARGS,     smt2lib_bvsle_doc},
  {"bvslt",       smt2lib_bvslt,      METH_VARARGS,     smt2lib_bvslt_doc},
  {"bvsmod",      smt2lib_bvsmod,     METH_VARARGS,     smt2lib_bvsmod_doc},
  {"bvsrem",      smt2lib_bvsrem,     METH_VARARGS,     smt2lib_bvsrem_doc},
  {"bvsub",       smt2lib_bvsub,      METH_VARARGS,     smt2lib_bvsub_doc},
  {"bvtrue",      smt2lib_bvtrue,     METH_NOARGS,      smt2lib_bvtrue_doc},
  {"bvudiv",      smt2lib_bvudiv,     METH_VARARGS,     smt2lib_bvudiv_doc},
  {"bvuge",       smt2lib_bvuge,      METH_VARARGS,     smt2lib_bvuge_doc},
  {"bvugt",       smt2lib_bvugt,      METH_VARARGS,     smt2lib_bvugt_doc},
  {"bvule",       smt2lib_bvule,      METH_VARARGS,     smt2lib_bvule_doc},
  {"bvult",       smt2lib_bvult,      METH_VARARGS,     smt2lib_bvult_doc},
  {"bvurem",      smt2lib_bvurem,     METH_VARARGS,     smt2lib_bvurem_doc},
  {"bvxnor",      smt2lib_bvxnor,     METH_VARARGS,     smt2lib_bvxnor_doc},
  {"bvxor",       smt2lib_bvxor,      METH_VARARGS,     smt2lib_bvxor_doc},
  {"distinct",    smt2lib_distinct,   METH_VARARGS,     smt2lib_distinct_doc},
  {"compound",    smt2lib_compound,   METH_O,           smt2lib_compound_doc},
  {"equal",       smt2lib_equal,      METH_VARARGS,     smt2lib_equal_doc},
  {"extract",     smt2lib_extract,    METH_VARARGS,     smt2lib_extract_doc},
  {"ite",         smt2lib_ite,        METH_VARARGS,     smt2lib_ite_doc},
  {"smtAssert",   smt2lib_smtAssert,  METH_O,           smt2lib_smtAssert_doc},
  {"string",      smt2lib_string,     METH_O,           smt2lib_string_doc},
  {"sx",          smt2lib_sx,         METH_VARARGS,     smt2lib_sx_doc},
  {"variable",    smt2lib_variable,   METH_O,           smt2lib_variable_doc},
  {"zx",          smt2lib_zx,         METH_VARARGS,     smt2lib_zx_doc},
  {nullptr,       nullptr,            0,                nullptr}
};

#endif /* LIGHT_VERSION */

