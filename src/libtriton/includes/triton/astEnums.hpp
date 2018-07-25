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
      ASSERT_NODE = 3,                /*!< (assert x) */
      BVADD_NODE = 5,                 /*!< (bvadd x y) */
      BVAND_NODE = 7,                 /*!< (bvand x y) */
      BVASHR_NODE = 12,               /*!< (bvashr x y) */
      BVLSHR_NODE = 17,               /*!< (bvlshr x y) */
      BVMUL_NODE = 19,                /*!< (bvmul x y) */
      BVNAND_NODE = 23,               /*!< (bvnand x y) */
      BVNEG_NODE = 29,                /*!< (bvneg x) */
      BVNOR_NODE = 31,                /*!< (bvnor x y) */
      BVNOT_NODE = 37,                /*!< (bvnot x) */
      BVOR_NODE = 41,                 /*!< (bvor x y) */
      BVROL_NODE = 43,                /*!< ((_ rotate_left x) y) */
      BVROR_NODE = 47,                /*!< ((_ rotate_right x) y) */
      BVSDIV_NODE = 53,               /*!< (bvsdiv x y) */
      BVSGE_NODE = 59,                /*!< (bvsge x y) */
      BVSGT_NODE = 61,                /*!< (bvsgt x y) */
      BVSHL_NODE = 67,                /*!< (bvshl x y) */
      BVSLE_NODE = 71,                /*!< (bvsle x y) */
      BVSLT_NODE = 73,                /*!< (bvslt x y) */
      BVSMOD_NODE = 79,               /*!< (bvsmod x y) */
      BVSREM_NODE = 83,               /*!< (bvsrem x y) */
      BVSUB_NODE = 89,                /*!< (bvsub x y) */
      BVUDIV_NODE = 97,               /*!< (bvudiv x y) */
      BVUGE_NODE = 101,               /*!< (bvuge x y) */
      BVUGT_NODE = 103,               /*!< (bvugt x y) */
      BVULE_NODE = 107,               /*!< (bvule x y) */
      BVULT_NODE = 109,               /*!< (bvult x y) */
      BVUREM_NODE = 113,              /*!< (bvurem x y) */
      BVXNOR_NODE = 127,              /*!< (bvxnor x y) */
      BVXOR_NODE = 131,               /*!< (bvxor x y) */
      BV_NODE = 137,                  /*!< (_ bvx y) */
      COMPOUND_NODE = 139,            /*!< A compound of nodes */
      CONCAT_NODE = 149,              /*!< (concat x y z ...) */
      DECIMAL_NODE = 151,             /*!< Decimal node */
      DECLARE_NODE = 157,             /*!< (declare-fun <var_name> () (_ BitVec <var_size>)) */
      DISTINCT_NODE = 163,            /*!< (distinct x y) */
      EQUAL_NODE = 167,               /*!< (= x y) */
      EXTRACT_NODE = 173,             /*!< ((_ extract x y) z) */
      ITE_NODE = 181,                 /*!< (ite x y z) */
      LAND_NODE = 191,                /*!< (and x y) */
      LET_NODE = 193,                 /*!< (let ((x y)) z) */
      LNOT_NODE = 197,                /*!< (and x y) */
      LOR_NODE = 199,                 /*!< (or x y) */
      REFERENCE_NODE = 223,           /*!< Reference node */
      STRING_NODE = 227,              /*!< String node */
      SX_NODE = 229,                  /*!< ((_ sign_extend x) y) */
      VARIABLE_NODE = 233,            /*!< Variable node */
      ZX_NODE = 239,                  /*!< ((_ zero_extend x) y) */
      ARRAY_NODE = 241,               /*!< (Array (_ BitVec addrSize) (_ BitVec 8)) */
      SELECT_NODE = 251,              /*!< (select a i) */
      STORE_NODE = 257                /*!< (store a i v) */
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};


#endif /* TRITON_ASTENUMS_H */
