//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ASTENUMS_H
#define TRITON_ASTENUMS_H



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The AST namespace
  namespace ast {
  /*!
   *  \ingroup triton
   *  \addtogroup ast
   *  @{
   */

    /*! Enumerates all kinds of node. Must be prime numbers. */
    enum kind_e {
      UNDEFINED_NODE = 0,             /*!< Unknown node */
      ASSERT_NODE = 2,                /*!< (assert x) */
      BVADD_NODE = 3,                 /*!< (bvadd x y) */
      BVAND_NODE = 5,                 /*!< (bvand x y) */
      BVASHR_NODE = 7,                /*!< (bvashr x y) */
      BVDECL_NODE = 11,               /*!< (_ BitVec x) */
      BVLSHR_NODE = 13,               /*!< (bvlshr x y) */
      BVMUL_NODE = 17,                /*!< (bvmul x y) */
      BVNAND_NODE = 19,               /*!< (bvnand x y) */
      BVNEG_NODE = 23,                /*!< (bvneg x) */
      BVNOR_NODE = 29,                /*!< (bvnor x y) */
      BVNOT_NODE = 31,                /*!< (bvnot x) */
      BVOR_NODE = 37,                 /*!< (bvor x y) */
      BVROL_NODE = 41,                /*!< ((_ rotate_left x) y) */
      BVROR_NODE = 43,                /*!< ((_ rotate_right x) y) */
      BVSDIV_NODE = 47,               /*!< (bvsdiv x y) */
      BVSGE_NODE = 53,                /*!< (bvsge x y) */
      BVSGT_NODE = 59,                /*!< (bvsgt x y) */
      BVSHL_NODE = 61,                /*!< (bvshl x y) */
      BVSLE_NODE = 67,                /*!< (bvslr x y) */
      BVSLT_NODE = 71,                /*!< (bvslt x y) */
      BVSMOD_NODE = 73,               /*!< (bvsmod x y) */
      BVSREM_NODE = 79,               /*!< (bvsrem x y) */
      BVSUB_NODE = 83,                /*!< (bvsub x y) */
      BVUDIV_NODE = 89,               /*!< (bvudiv x y) */
      BVUGE_NODE = 97,                /*!< (bvuge x y) */
      BVUGT_NODE = 101,               /*!< (bvugt x y) */
      BVULE_NODE = 103,               /*!< (bvule x y) */
      BVULT_NODE = 107,               /*!< (bvult x y) */
      BVUREM_NODE = 109,              /*!< (bvurem x y) */
      BVXNOR_NODE = 113,              /*!< (bvxnor x y) */
      BVXOR_NODE = 127,               /*!< (bvxor x y) */
      BV_NODE = 131,                  /*!< (_ bvx y) */
      COMPOUND_NODE = 139,            /*!< Coumpound of several nodes */
      CONCAT_NODE = 149,              /*!< (concat x y z ...) */
      DECIMAL_NODE = 151,             /*!< Decimal node */
      DECLARE_FUNCTION_NODE = 157,    /*!< (declare-fun x () (_ BitVec y)) */
      DISTINCT_NODE = 163,            /*!< (distinct x y) */
      EQUAL_NODE = 167,               /*!< (= x y) */
      EXTRACT_NODE = 173,             /*!< ((_ extract x y) z) */
      FUNCTION_NODE = 179,            /*!< (define-fun w (x) y z) */
      ITE_NODE = 181,                 /*!< (ite x y z) */
      LAND_NODE = 191,                /*!< (and x y) */
      LET_NODE = 193,                 /*!< (let ((x y)) z) */
      LNOT_NODE = 197,                /*!< (and x y) */
      LOR_NODE = 199,                 /*!< (or x y) */
      PARAM_NODE = 211,               /*!< (x y) */
      REFERENCE_NODE = 223,           /*!< Reference node */
      STRING_NODE = 227,              /*!< String node */
      SX_NODE = 229,                  /*!< ((_ sign_extend x) y) */
      VARIABLE_NODE = 233,            /*!< Variable node */
      ZX_NODE = 239                   /*!< ((_ zero_extend x) y) */
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};


#endif /* TRITON_ASTENUMS_H */

