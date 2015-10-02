/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <SMT2Lib.h>


void initSmtAstNodeEnv(PyObject *idSmtAstNodeClassDict) {
  PyDict_SetItemString(idSmtAstNodeClassDict, "ASSERT", PyInt_FromLong(smt2lib::ASSERT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVADD", PyInt_FromLong(smt2lib::BVADD_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVAND", PyInt_FromLong(smt2lib::BVAND_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVASHR", PyInt_FromLong(smt2lib::BVASHR_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVLSHR", PyInt_FromLong(smt2lib::BVLSHR_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVMUL", PyInt_FromLong(smt2lib::BVMUL_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVNAND", PyInt_FromLong(smt2lib::BVNAND_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVNEG", PyInt_FromLong(smt2lib::BVNEG_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVNOR", PyInt_FromLong(smt2lib::BVNOR_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVNOT", PyInt_FromLong(smt2lib::BVNOT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVOR", PyInt_FromLong(smt2lib::BVOR_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVROL", PyInt_FromLong(smt2lib::BVROL_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVROR", PyInt_FromLong(smt2lib::BVROR_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSDIV", PyInt_FromLong(smt2lib::BVSDIV_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSGE", PyInt_FromLong(smt2lib::BVSGE_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSGT", PyInt_FromLong(smt2lib::BVSGT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSHL", PyInt_FromLong(smt2lib::BVSHL_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSLE", PyInt_FromLong(smt2lib::BVSLE_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSLT", PyInt_FromLong(smt2lib::BVSLT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSMOD", PyInt_FromLong(smt2lib::BVSMOD_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSREM", PyInt_FromLong(smt2lib::BVSREM_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSUB", PyInt_FromLong(smt2lib::BVSUB_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVUDIV", PyInt_FromLong(smt2lib::BVUDIV_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVUGE", PyInt_FromLong(smt2lib::BVUGE_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVUGT", PyInt_FromLong(smt2lib::BVUGT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVULE", PyInt_FromLong(smt2lib::BVULE_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVULT", PyInt_FromLong(smt2lib::BVULT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVUREM", PyInt_FromLong(smt2lib::BVUREM_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVXNOR", PyInt_FromLong(smt2lib::BVXNOR_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVXOR", PyInt_FromLong(smt2lib::BVXOR_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BV", PyInt_FromLong(smt2lib::BV_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "COMPOUND", PyInt_FromLong(smt2lib::COMPOUND_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "CONCAT", PyInt_FromLong(smt2lib::CONCAT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "DECIMAL", PyInt_FromLong(smt2lib::DECIMAL_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "DECLARE", PyInt_FromLong(smt2lib::DECLARE_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "DISTINCT", PyInt_FromLong(smt2lib::DISTINCT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "EQUAL", PyInt_FromLong(smt2lib::EQUAL_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "EXTRACT", PyInt_FromLong(smt2lib::EXTRACT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "ITE", PyInt_FromLong(smt2lib::ITE_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "REFERENCE", PyInt_FromLong(smt2lib::REFERENCE_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "STRING", PyInt_FromLong(smt2lib::STRING_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "SX", PyInt_FromLong(smt2lib::SX_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "UNDEFINED", PyInt_FromLong(smt2lib::UNDEFINED_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "VARIABLE", PyInt_FromLong(smt2lib::VARIABLE_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "ZX", PyInt_FromLong(smt2lib::ZX_NODE));
}

#endif

