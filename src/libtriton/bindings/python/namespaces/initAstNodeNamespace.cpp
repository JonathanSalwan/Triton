//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/ast.hpp>
#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>



/*! \page py_AST_NODE_page AST_NODE
    \brief [**python api**] All information about the AST_NODE python namespace.

\tableofcontents

\section AST_NODE_py_description Description
<hr>

The AST_NODE namespace contains all kinds of node.

\section AST_NODE_py_api Python API - Items of the AST_NODE namespace
<hr>

- **AST_NODE.ASSERT**
- **AST_NODE.BV**
- **AST_NODE.BVADD**
- **AST_NODE.BVAND**
- **AST_NODE.BVASHR**
- **AST_NODE.BVDECL**
- **AST_NODE.BVLSHR**
- **AST_NODE.BVMUL**
- **AST_NODE.BVNAND**
- **AST_NODE.BVNEG**
- **AST_NODE.BVNOR**
- **AST_NODE.BVNOT**
- **AST_NODE.BVOR**
- **AST_NODE.BVROL**
- **AST_NODE.BVROR**
- **AST_NODE.BVSDIV**
- **AST_NODE.BVSGE**
- **AST_NODE.BVSGT**
- **AST_NODE.BVSHL**
- **AST_NODE.BVSLE**
- **AST_NODE.BVSLT**
- **AST_NODE.BVSMOD**
- **AST_NODE.BVSREM**
- **AST_NODE.BVSUB**
- **AST_NODE.BVUDIV**
- **AST_NODE.BVUGE**
- **AST_NODE.BVUGT**
- **AST_NODE.BVULE**
- **AST_NODE.BVULT**
- **AST_NODE.BVUREM**
- **AST_NODE.BVXNOR**
- **AST_NODE.BVXOR**
- **AST_NODE.COMPOUND**
- **AST_NODE.CONCAT**
- **AST_NODE.DECIMAL**
- **AST_NODE.DECLARE_FUNCTION**
- **AST_NODE.DISTINCT**
- **AST_NODE.EQUAL**
- **AST_NODE.EXTRACT**
- **AST_NODE.FUNCTION**
- **AST_NODE.ITE**
- **AST_NODE.LAND**
- **AST_NODE.LET**
- **AST_NODE.LNOT**
- **AST_NODE.LOR**
- **AST_NODE.PARAM**
- **AST_NODE.REFERENCE**
- **AST_NODE.STRING**
- **AST_NODE.SX**
- **AST_NODE.UNDEFINED**
- **AST_NODE.VARIABLE**
- **AST_NODE.ZX**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initAstNodeNamespace(PyObject* astNodeDict) {
        PyDict_SetItemString(astNodeDict, "ASSERT",            PyLong_FromUint32(triton::ast::ASSERT_NODE));
        PyDict_SetItemString(astNodeDict, "BV",                PyLong_FromUint32(triton::ast::BV_NODE));
        PyDict_SetItemString(astNodeDict, "BVADD",             PyLong_FromUint32(triton::ast::BVADD_NODE));
        PyDict_SetItemString(astNodeDict, "BVAND",             PyLong_FromUint32(triton::ast::BVAND_NODE));
        PyDict_SetItemString(astNodeDict, "BVASHR",            PyLong_FromUint32(triton::ast::BVASHR_NODE));
        PyDict_SetItemString(astNodeDict, "BVDECL",            PyLong_FromUint32(triton::ast::BVDECL_NODE));
        PyDict_SetItemString(astNodeDict, "BVLSHR",            PyLong_FromUint32(triton::ast::BVLSHR_NODE));
        PyDict_SetItemString(astNodeDict, "BVMUL",             PyLong_FromUint32(triton::ast::BVMUL_NODE));
        PyDict_SetItemString(astNodeDict, "BVNAND",            PyLong_FromUint32(triton::ast::BVNAND_NODE));
        PyDict_SetItemString(astNodeDict, "BVNEG",             PyLong_FromUint32(triton::ast::BVNEG_NODE));
        PyDict_SetItemString(astNodeDict, "BVNOR",             PyLong_FromUint32(triton::ast::BVNOR_NODE));
        PyDict_SetItemString(astNodeDict, "BVNOT",             PyLong_FromUint32(triton::ast::BVNOT_NODE));
        PyDict_SetItemString(astNodeDict, "BVOR",              PyLong_FromUint32(triton::ast::BVOR_NODE));
        PyDict_SetItemString(astNodeDict, "BVROL",             PyLong_FromUint32(triton::ast::BVROL_NODE));
        PyDict_SetItemString(astNodeDict, "BVROR",             PyLong_FromUint32(triton::ast::BVROR_NODE));
        PyDict_SetItemString(astNodeDict, "BVSDIV",            PyLong_FromUint32(triton::ast::BVSDIV_NODE));
        PyDict_SetItemString(astNodeDict, "BVSGE",             PyLong_FromUint32(triton::ast::BVSGE_NODE));
        PyDict_SetItemString(astNodeDict, "BVSGT",             PyLong_FromUint32(triton::ast::BVSGT_NODE));
        PyDict_SetItemString(astNodeDict, "BVSHL",             PyLong_FromUint32(triton::ast::BVSHL_NODE));
        PyDict_SetItemString(astNodeDict, "BVSLE",             PyLong_FromUint32(triton::ast::BVSLE_NODE));
        PyDict_SetItemString(astNodeDict, "BVSLT",             PyLong_FromUint32(triton::ast::BVSLT_NODE));
        PyDict_SetItemString(astNodeDict, "BVSMOD",            PyLong_FromUint32(triton::ast::BVSMOD_NODE));
        PyDict_SetItemString(astNodeDict, "BVSREM",            PyLong_FromUint32(triton::ast::BVSREM_NODE));
        PyDict_SetItemString(astNodeDict, "BVSUB",             PyLong_FromUint32(triton::ast::BVSUB_NODE));
        PyDict_SetItemString(astNodeDict, "BVUDIV",            PyLong_FromUint32(triton::ast::BVUDIV_NODE));
        PyDict_SetItemString(astNodeDict, "BVUGE",             PyLong_FromUint32(triton::ast::BVUGE_NODE));
        PyDict_SetItemString(astNodeDict, "BVUGT",             PyLong_FromUint32(triton::ast::BVUGT_NODE));
        PyDict_SetItemString(astNodeDict, "BVULE",             PyLong_FromUint32(triton::ast::BVULE_NODE));
        PyDict_SetItemString(astNodeDict, "BVULT",             PyLong_FromUint32(triton::ast::BVULT_NODE));
        PyDict_SetItemString(astNodeDict, "BVUREM",            PyLong_FromUint32(triton::ast::BVUREM_NODE));
        PyDict_SetItemString(astNodeDict, "BVXNOR",            PyLong_FromUint32(triton::ast::BVXNOR_NODE));
        PyDict_SetItemString(astNodeDict, "BVXOR",             PyLong_FromUint32(triton::ast::BVXOR_NODE));
        PyDict_SetItemString(astNodeDict, "COMPOUND",          PyLong_FromUint32(triton::ast::COMPOUND_NODE));
        PyDict_SetItemString(astNodeDict, "CONCAT",            PyLong_FromUint32(triton::ast::CONCAT_NODE));
        PyDict_SetItemString(astNodeDict, "DECIMAL",           PyLong_FromUint32(triton::ast::DECIMAL_NODE));
        PyDict_SetItemString(astNodeDict, "DECLARE_FUNCTION",  PyLong_FromUint32(triton::ast::DECLARE_FUNCTION_NODE));
        PyDict_SetItemString(astNodeDict, "DISTINCT",          PyLong_FromUint32(triton::ast::DISTINCT_NODE));
        PyDict_SetItemString(astNodeDict, "EQUAL",             PyLong_FromUint32(triton::ast::EQUAL_NODE));
        PyDict_SetItemString(astNodeDict, "EXTRACT",           PyLong_FromUint32(triton::ast::EXTRACT_NODE));
        PyDict_SetItemString(astNodeDict, "FUNCTION",          PyLong_FromUint32(triton::ast::FUNCTION_NODE));
        PyDict_SetItemString(astNodeDict, "ITE",               PyLong_FromUint32(triton::ast::ITE_NODE));
        PyDict_SetItemString(astNodeDict, "LAND",              PyLong_FromUint32(triton::ast::LAND_NODE));
        PyDict_SetItemString(astNodeDict, "LET",               PyLong_FromUint32(triton::ast::LET_NODE));
        PyDict_SetItemString(astNodeDict, "LNOT",              PyLong_FromUint32(triton::ast::LNOT_NODE));
        PyDict_SetItemString(astNodeDict, "LOR",               PyLong_FromUint32(triton::ast::LOR_NODE));
        PyDict_SetItemString(astNodeDict, "PARAM",             PyLong_FromUint32(triton::ast::PARAM_NODE));
        PyDict_SetItemString(astNodeDict, "REFERENCE",         PyLong_FromUint32(triton::ast::REFERENCE_NODE));
        PyDict_SetItemString(astNodeDict, "STRING",            PyLong_FromUint32(triton::ast::STRING_NODE));
        PyDict_SetItemString(astNodeDict, "SX",                PyLong_FromUint32(triton::ast::SX_NODE));
        PyDict_SetItemString(astNodeDict, "UNDEFINED",         PyLong_FromUint32(triton::ast::UNDEFINED_NODE));
        PyDict_SetItemString(astNodeDict, "VARIABLE",          PyLong_FromUint32(triton::ast::VARIABLE_NODE));
        PyDict_SetItemString(astNodeDict, "ZX",                PyLong_FromUint32(triton::ast::ZX_NODE));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
