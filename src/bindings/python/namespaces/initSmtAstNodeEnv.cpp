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
  PyDict_SetItemString(idSmtAstNodeClassDict, "ASSERT", PyLong_FromUint(smt2lib::ASSERT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVADD", PyLong_FromUint(smt2lib::BVADD_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVAND", PyLong_FromUint(smt2lib::BVAND_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVASHR", PyLong_FromUint(smt2lib::BVASHR_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVLSHR", PyLong_FromUint(smt2lib::BVLSHR_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVMUL", PyLong_FromUint(smt2lib::BVMUL_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVNAND", PyLong_FromUint(smt2lib::BVNAND_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVNEG", PyLong_FromUint(smt2lib::BVNEG_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVNOR", PyLong_FromUint(smt2lib::BVNOR_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVNOT", PyLong_FromUint(smt2lib::BVNOT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVOR", PyLong_FromUint(smt2lib::BVOR_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVROL", PyLong_FromUint(smt2lib::BVROL_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVROR", PyLong_FromUint(smt2lib::BVROR_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSDIV", PyLong_FromUint(smt2lib::BVSDIV_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSGE", PyLong_FromUint(smt2lib::BVSGE_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSGT", PyLong_FromUint(smt2lib::BVSGT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSHL", PyLong_FromUint(smt2lib::BVSHL_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSLE", PyLong_FromUint(smt2lib::BVSLE_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSLT", PyLong_FromUint(smt2lib::BVSLT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSMOD", PyLong_FromUint(smt2lib::BVSMOD_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSREM", PyLong_FromUint(smt2lib::BVSREM_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVSUB", PyLong_FromUint(smt2lib::BVSUB_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVUDIV", PyLong_FromUint(smt2lib::BVUDIV_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVUGE", PyLong_FromUint(smt2lib::BVUGE_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVUGT", PyLong_FromUint(smt2lib::BVUGT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVULE", PyLong_FromUint(smt2lib::BVULE_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVULT", PyLong_FromUint(smt2lib::BVULT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVUREM", PyLong_FromUint(smt2lib::BVUREM_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVXNOR", PyLong_FromUint(smt2lib::BVXNOR_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BVXOR", PyLong_FromUint(smt2lib::BVXOR_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "BV", PyLong_FromUint(smt2lib::BV_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "COMPOUND", PyLong_FromUint(smt2lib::COMPOUND_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "CONCAT", PyLong_FromUint(smt2lib::CONCAT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "DECIMAL", PyLong_FromUint(smt2lib::DECIMAL_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "DECLARE", PyLong_FromUint(smt2lib::DECLARE_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "DISTINCT", PyLong_FromUint(smt2lib::DISTINCT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "EQUAL", PyLong_FromUint(smt2lib::EQUAL_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "EXTRACT", PyLong_FromUint(smt2lib::EXTRACT_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "ITE", PyLong_FromUint(smt2lib::ITE_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "REFERENCE", PyLong_FromUint(smt2lib::REFERENCE_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "STRING", PyLong_FromUint(smt2lib::STRING_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "SX", PyLong_FromUint(smt2lib::SX_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "UNDEFINED", PyLong_FromUint(smt2lib::UNDEFINED_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "VARIABLE", PyLong_FromUint(smt2lib::VARIABLE_NODE));
  PyDict_SetItemString(idSmtAstNodeClassDict, "ZX", PyLong_FromUint(smt2lib::ZX_NODE));
}

#endif

