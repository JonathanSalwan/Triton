//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <pythonBindings.hpp>
#include <pythonUtils.hpp>
#include <smt2lib.hpp>

#ifdef __unix__
  #include <python2.7/Python.h>
#elif _WIN32
  #include <Python.h>
#endif



/*! \page py_SMT_AST_NODE_page SMT_AST_NODE
    \brief [**python api**] All information about the SMT_AST_NODE python namespace.

\tableofcontents

\section SMT_AST_NODE_py_description Description
<hr>

The SMT_AST_NODE namespace contains all kinds of node.

\section SMT_AST_NODE_py_api Python API - Items of the SMT_AST_NODE namespace
<hr>

- **SMT_AST_NODE.ASSERT**
- **SMT_AST_NODE.BVADD**
- **SMT_AST_NODE.BVAND**
- **SMT_AST_NODE.BVASHR**
- **SMT_AST_NODE.BVLSHR**
- **SMT_AST_NODE.BVMUL**
- **SMT_AST_NODE.BVNAND**
- **SMT_AST_NODE.BVNEG**
- **SMT_AST_NODE.BVNOR**
- **SMT_AST_NODE.BVNOT**
- **SMT_AST_NODE.BVOR**
- **SMT_AST_NODE.BVROL**
- **SMT_AST_NODE.BVROR**
- **SMT_AST_NODE.BVSDIV**
- **SMT_AST_NODE.BVSGE**
- **SMT_AST_NODE.BVSGT**
- **SMT_AST_NODE.BVSHL**
- **SMT_AST_NODE.BVSLE**
- **SMT_AST_NODE.BVSLT**
- **SMT_AST_NODE.BVSMOD**
- **SMT_AST_NODE.BVSREM**
- **SMT_AST_NODE.BVSUB**
- **SMT_AST_NODE.BVUDIV**
- **SMT_AST_NODE.BVUGE**
- **SMT_AST_NODE.BVUGT**
- **SMT_AST_NODE.BVULE**
- **SMT_AST_NODE.BVULT**
- **SMT_AST_NODE.BVUREM**
- **SMT_AST_NODE.BVXNOR**
- **SMT_AST_NODE.BVXOR**
- **SMT_AST_NODE.BV**
- **SMT_AST_NODE.COMPOUND**
- **SMT_AST_NODE.CONCAT**
- **SMT_AST_NODE.DECIMAL**
- **SMT_AST_NODE.DECLARE**
- **SMT_AST_NODE.DISTINCT**
- **SMT_AST_NODE.EQUAL**
- **SMT_AST_NODE.EXTRACT**
- **SMT_AST_NODE.ITE**
- **SMT_AST_NODE.LAND**
- **SMT_AST_NODE.LNOT**
- **SMT_AST_NODE.LOR**
- **SMT_AST_NODE.REFERENCE**
- **SMT_AST_NODE.STRING**
- **SMT_AST_NODE.SX**
- **SMT_AST_NODE.UNDEFINED**
- **SMT_AST_NODE.VARIABLE**
- **SMT_AST_NODE.ZX**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initSmtAstNodeNamespace(PyObject* smtAstNodeDict) {

        PyDict_SetItemString(smtAstNodeDict, "ASSERT", PyLong_FromUint(triton::smt2lib::ASSERT_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVADD", PyLong_FromUint(triton::smt2lib::BVADD_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVAND", PyLong_FromUint(triton::smt2lib::BVAND_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVASHR", PyLong_FromUint(triton::smt2lib::BVASHR_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVLSHR", PyLong_FromUint(triton::smt2lib::BVLSHR_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVMUL", PyLong_FromUint(triton::smt2lib::BVMUL_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVNAND", PyLong_FromUint(triton::smt2lib::BVNAND_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVNEG", PyLong_FromUint(triton::smt2lib::BVNEG_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVNOR", PyLong_FromUint(triton::smt2lib::BVNOR_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVNOT", PyLong_FromUint(triton::smt2lib::BVNOT_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVOR", PyLong_FromUint(triton::smt2lib::BVOR_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVROL", PyLong_FromUint(triton::smt2lib::BVROL_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVROR", PyLong_FromUint(triton::smt2lib::BVROR_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVSDIV", PyLong_FromUint(triton::smt2lib::BVSDIV_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVSGE", PyLong_FromUint(triton::smt2lib::BVSGE_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVSGT", PyLong_FromUint(triton::smt2lib::BVSGT_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVSHL", PyLong_FromUint(triton::smt2lib::BVSHL_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVSLE", PyLong_FromUint(triton::smt2lib::BVSLE_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVSLT", PyLong_FromUint(triton::smt2lib::BVSLT_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVSMOD", PyLong_FromUint(triton::smt2lib::BVSMOD_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVSREM", PyLong_FromUint(triton::smt2lib::BVSREM_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVSUB", PyLong_FromUint(triton::smt2lib::BVSUB_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVUDIV", PyLong_FromUint(triton::smt2lib::BVUDIV_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVUGE", PyLong_FromUint(triton::smt2lib::BVUGE_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVUGT", PyLong_FromUint(triton::smt2lib::BVUGT_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVULE", PyLong_FromUint(triton::smt2lib::BVULE_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVULT", PyLong_FromUint(triton::smt2lib::BVULT_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVUREM", PyLong_FromUint(triton::smt2lib::BVUREM_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVXNOR", PyLong_FromUint(triton::smt2lib::BVXNOR_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BVXOR", PyLong_FromUint(triton::smt2lib::BVXOR_NODE));
        PyDict_SetItemString(smtAstNodeDict, "BV", PyLong_FromUint(triton::smt2lib::BV_NODE));
        PyDict_SetItemString(smtAstNodeDict, "COMPOUND", PyLong_FromUint(triton::smt2lib::COMPOUND_NODE));
        PyDict_SetItemString(smtAstNodeDict, "CONCAT", PyLong_FromUint(triton::smt2lib::CONCAT_NODE));
        PyDict_SetItemString(smtAstNodeDict, "DECIMAL", PyLong_FromUint(triton::smt2lib::DECIMAL_NODE));
        PyDict_SetItemString(smtAstNodeDict, "DECLARE", PyLong_FromUint(triton::smt2lib::DECLARE_NODE));
        PyDict_SetItemString(smtAstNodeDict, "DISTINCT", PyLong_FromUint(triton::smt2lib::DISTINCT_NODE));
        PyDict_SetItemString(smtAstNodeDict, "EQUAL", PyLong_FromUint(triton::smt2lib::EQUAL_NODE));
        PyDict_SetItemString(smtAstNodeDict, "EXTRACT", PyLong_FromUint(triton::smt2lib::EXTRACT_NODE));
        PyDict_SetItemString(smtAstNodeDict, "ITE", PyLong_FromUint(triton::smt2lib::ITE_NODE));
        PyDict_SetItemString(smtAstNodeDict, "LAND", PyLong_FromUint(triton::smt2lib::LAND_NODE));
        PyDict_SetItemString(smtAstNodeDict, "LNOT", PyLong_FromUint(triton::smt2lib::LNOT_NODE));
        PyDict_SetItemString(smtAstNodeDict, "LOR", PyLong_FromUint(triton::smt2lib::LOR_NODE));
        PyDict_SetItemString(smtAstNodeDict, "REFERENCE", PyLong_FromUint(triton::smt2lib::REFERENCE_NODE));
        PyDict_SetItemString(smtAstNodeDict, "STRING", PyLong_FromUint(triton::smt2lib::STRING_NODE));
        PyDict_SetItemString(smtAstNodeDict, "SX", PyLong_FromUint(triton::smt2lib::SX_NODE));
        PyDict_SetItemString(smtAstNodeDict, "UNDEFINED", PyLong_FromUint(triton::smt2lib::UNDEFINED_NODE));
        PyDict_SetItemString(smtAstNodeDict, "VARIABLE", PyLong_FromUint(triton::smt2lib::VARIABLE_NODE));
        PyDict_SetItemString(smtAstNodeDict, "ZX", PyLong_FromUint(triton::smt2lib::ZX_NODE));

      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
