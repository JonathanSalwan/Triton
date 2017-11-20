//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>

// FIXME: Where should be done the python binding for tritonast?
#include <tritonast/nodes.hpp>



/*! \page py_AST_NODE_page AST_NODE
    \brief [**python api**] All information about the AST_NODE python namespace.

\tableofcontents

\section AST_NODE_py_description Description
<hr>

The AST_NODE namespace contains all kinds of node.

\section AST_NODE_py_api Python API - Items of the AST_NODE namespace
<hr>

- **AST_NODE.BV**
- **AST_NODE.BVADD**
- **AST_NODE.BVAND**
- **AST_NODE.BVASHR**
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
- **AST_NODE.CONCAT**
- **AST_NODE.DECIMAL**
- **AST_NODE.DISTINCT**
- **AST_NODE.EQUAL**
- **AST_NODE.EXTRACT**
- **AST_NODE.ITE**
- **AST_NODE.LAND**
- **AST_NODE.LET**
- **AST_NODE.LNOT**
- **AST_NODE.LOR**
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
        PyDict_SetItemStringSteal(astNodeDict, "BV",                PyLong_FromUint32(triton::ast::BV_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVADD",             PyLong_FromUint32(triton::ast::BVADD_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVAND",             PyLong_FromUint32(triton::ast::BVAND_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVASHR",            PyLong_FromUint32(triton::ast::BVASHR_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVLSHR",            PyLong_FromUint32(triton::ast::BVLSHR_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVMUL",             PyLong_FromUint32(triton::ast::BVMUL_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVNAND",            PyLong_FromUint32(triton::ast::BVNAND_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVNEG",             PyLong_FromUint32(triton::ast::BVNEG_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVNOR",             PyLong_FromUint32(triton::ast::BVNOR_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVNOT",             PyLong_FromUint32(triton::ast::BVNOT_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVOR",              PyLong_FromUint32(triton::ast::BVOR_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVROL",             PyLong_FromUint32(triton::ast::BVROL_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVROR",             PyLong_FromUint32(triton::ast::BVROR_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVSDIV",            PyLong_FromUint32(triton::ast::BVSDIV_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVSGE",             PyLong_FromUint32(triton::ast::BVSGE_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVSGT",             PyLong_FromUint32(triton::ast::BVSGT_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVSHL",             PyLong_FromUint32(triton::ast::BVSHL_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVSLE",             PyLong_FromUint32(triton::ast::BVSLE_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVSLT",             PyLong_FromUint32(triton::ast::BVSLT_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVSMOD",            PyLong_FromUint32(triton::ast::BVSMOD_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVSREM",            PyLong_FromUint32(triton::ast::BVSREM_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVSUB",             PyLong_FromUint32(triton::ast::BVSUB_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVUDIV",            PyLong_FromUint32(triton::ast::BVUDIV_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVUGE",             PyLong_FromUint32(triton::ast::BVUGE_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVUGT",             PyLong_FromUint32(triton::ast::BVUGT_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVULE",             PyLong_FromUint32(triton::ast::BVULE_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVULT",             PyLong_FromUint32(triton::ast::BVULT_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVUREM",            PyLong_FromUint32(triton::ast::BVUREM_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVXNOR",            PyLong_FromUint32(triton::ast::BVXNOR_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "BVXOR",             PyLong_FromUint32(triton::ast::BVXOR_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "CONCAT",            PyLong_FromUint32(triton::ast::CONCAT_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "DECIMAL",           PyLong_FromUint32(triton::ast::DECIMAL_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "DISTINCT",          PyLong_FromUint32(triton::ast::DISTINCT_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "EQUAL",             PyLong_FromUint32(triton::ast::EQUAL_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "EXTRACT",           PyLong_FromUint32(triton::ast::EXTRACT_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "ITE",               PyLong_FromUint32(triton::ast::ITE_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "LAND",              PyLong_FromUint32(triton::ast::LAND_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "LET",               PyLong_FromUint32(triton::ast::LET_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "LNOT",              PyLong_FromUint32(triton::ast::LNOT_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "LOR",               PyLong_FromUint32(triton::ast::LOR_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "REFERENCE",         PyLong_FromUint32(triton::ast::REFERENCE_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "STRING",            PyLong_FromUint32(triton::ast::STRING_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "SX",                PyLong_FromUint32(triton::ast::SX_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "UNDEFINED",         PyLong_FromUint32(triton::ast::UNDEFINED_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "VARIABLE",          PyLong_FromUint32(triton::ast::VARIABLE_NODE));
        PyDict_SetItemStringSteal(astNodeDict, "ZX",                PyLong_FromUint32(triton::ast::ZX_NODE));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
