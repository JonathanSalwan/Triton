//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_ASTENUMS_HPP
#define TRITON_ASTENUMS_HPP

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

    /*! Enumerates all types of node. Must be prime numbers. */
    enum ast_e {
      INVALID_NODE   = 0,   /*!< Invalid node */
      ANY_NODE       = 0,   /*!< Any node */
      ASSERT_NODE    = 3,   /*!< (assert x) */
      BSWAP_NODE     = 5,   /*!< (bswap x) */
      BVADD_NODE     = 7,   /*!< (bvadd x y) */
      BVAND_NODE     = 13,  /*!< (bvand x y) */
      BVASHR_NODE    = 17,  /*!< (bvashr x y) */
      BVLSHR_NODE    = 19,  /*!< (bvlshr x y) */
      BVMUL_NODE     = 23,  /*!< (bvmul x y) */
      BVNAND_NODE    = 29,  /*!< (bvnand x y) */
      BVNEG_NODE     = 31,  /*!< (bvneg x) */
      BVNOR_NODE     = 37,  /*!< (bvnor x y) */
      BVNOT_NODE     = 41,  /*!< (bvnot x) */
      BVOR_NODE      = 43,  /*!< (bvor x y) */
      BVROL_NODE     = 47,  /*!< ((_ rotate_left x) y) */
      BVROR_NODE     = 53,  /*!< ((_ rotate_right x) y) */
      BVSDIV_NODE    = 59,  /*!< (bvsdiv x y) */
      BVSGE_NODE     = 61,  /*!< (bvsge x y) */
      BVSGT_NODE     = 67,  /*!< (bvsgt x y) */
      BVSHL_NODE     = 71,  /*!< (bvshl x y) */
      BVSLE_NODE     = 73,  /*!< (bvsle x y) */
      BVSLT_NODE     = 79,  /*!< (bvslt x y) */
      BVSMOD_NODE    = 83,  /*!< (bvsmod x y) */
      BVSREM_NODE    = 89,  /*!< (bvsrem x y) */
      BVSUB_NODE     = 97,  /*!< (bvsub x y) */
      BVUDIV_NODE    = 101, /*!< (bvudiv x y) */
      BVUGE_NODE     = 103, /*!< (bvuge x y) */
      BVUGT_NODE     = 107, /*!< (bvugt x y) */
      BVULE_NODE     = 109, /*!< (bvule x y) */
      BVULT_NODE     = 113, /*!< (bvult x y) */
      BVUREM_NODE    = 127, /*!< (bvurem x y) */
      BVXNOR_NODE    = 131, /*!< (bvxnor x y) */
      BVXOR_NODE     = 137, /*!< (bvxor x y) */
      BV_NODE        = 139, /*!< (_ bvx y) */
      COMPOUND_NODE  = 149, /*!< A compound of nodes */
      CONCAT_NODE    = 151, /*!< (concat x y z ...) */
      DECLARE_NODE   = 157, /*!< (declare-fun <var_name> () (_ BitVec <var_size>)) */
      DISTINCT_NODE  = 163, /*!< (distinct x y) */
      EQUAL_NODE     = 167, /*!< (= x y) */
      EXTRACT_NODE   = 173, /*!< ((_ extract x y) z) */
      FORALL_NODE    = 179, /*!< (forall ((x (_ BitVec <size>)), ...) body) */
      IFF_NODE       = 181, /*!< (iff x y) */
      INTEGER_NODE   = 191, /*!< Integer node */
      ITE_NODE       = 193, /*!< (ite x y z) */
      LAND_NODE      = 197, /*!< (and x y) */
      LET_NODE       = 199, /*!< (let ((x y)) z) */
      LNOT_NODE      = 211, /*!< (and x y) */
      LOR_NODE       = 223, /*!< (or x y) */
      LXOR_NODE      = 227, /*!< (xor x y) */
      REFERENCE_NODE = 229, /*!< Reference node */
      STRING_NODE    = 233, /*!< String node */
      SX_NODE        = 239, /*!< ((_ sign_extend x) y) */
      VARIABLE_NODE  = 241, /*!< Variable node */
      ZX_NODE        = 251, /*!< ((_ zero_extend x) y) */
      ARRAY_NODE     = 257, /*!< (Array (_ BitVec addrSize) (_ BitVec 8)) */
      SELECT_NODE    = 263, /*!< (select array index) */
      STORE_NODE     = 269, /*!< (store array index expr) */
    };

    //! The Representations namespace
    namespace representations {
      /*!
       *  \ingroup ast
       *  \addtogroup representations
       *  @{
       */

      //! All types of representation mode.
      enum mode_e {
        SMT_REPRESENTATION    = 0, /*!< SMT representation */
        PYTHON_REPRESENTATION = 1, /*!< Python representation */
        PCODE_REPRESENTATION  = 2, /*!< Pseudo Code representation */
        LAST_REPRESENTATION   = 3, /*!< Must be the last item */
      };

      /*! @} End of representations namespace */
    }; // namespace representations
    /*! @} End of ast namespace */
  }; // namespace ast
  /*! @} End of triton namespace */
}; // namespace triton

#endif /* TRITON_ASTENUMS_HPP */
