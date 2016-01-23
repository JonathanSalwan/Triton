//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SYMBOLICSUMMARY_H
#define TRITON_SYMBOLICSUMMARY_H

#include <list>

#include "smt2lib.hpp"
#include "tritonTypes.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Engines namespace
  namespace engines {
  /*!
   *  \ingroup triton
   *  \addtogroup engines
   *  @{
   */

    //! \module The Symbolic Execution namespace
    namespace symbolic {
    /*!
     *  \ingroup engines
     *  \addtogroup symbolic
     *  @{
     */

      //! Assert Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> assertSummaries;

      //! Bvadd Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvaddSummaries;

      //! Bvand Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvandSummaries;

      //! Bvashr Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvashrSummaries;

      //! Bvlshr Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvlshrSummaries;

      //! Bvmul Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvmulSummaries;

      //! Bvnand Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvnandSummaries;

      //! Bvneg Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvnegSummaries;

      //! Bvnor Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvnorSummaries;

      //! Bvnot Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvnotSummaries;

      //! Bvor Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvorSummaries;

      //! Bvrol Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvrolSummaries;

      //! Bvror Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvrorSummaries;

      //! Bvsdiv Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsdivSummariaes;

      //! Bvsge Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsgeSummaries;

      //! Bvsgt Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsgtSummaries;

      //! Bvshl Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvshlSummaries;

      //! Bvsle Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsleSummaries;

      //! Bvslt Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsltSummaries;

      //! Bvsmod Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsmodSummaries;

      //! Bvsrem Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsremSummaries;

      //! Bvsub Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsubSummaries;

      //! Bvudiv Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvudivSummaries;

      //! Bvuge Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvugeSummaries;

      //! Bvugt Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvugtSummaries;

      //! Bvule Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvuleSummaries;

      //! Bvult Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvultSummaries;

      //! Bvurem Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvuremSummaries;

      //! Bvxnor Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvxnorSummaries;

      //! Bvxor Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvxorSummaries;

      //! Bv Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvSummaries;

      //! Compound Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> compoundSummaries;

      //! Concat Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> concatSummaries;

      //! Decimal Summaries
      extern std::map<triton::uint128, triton::smt2lib::smtAstAbstractNode*> decimalSummaries;

      //! Declare Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> declareSummaries;

      //! Distinct Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> distinctSummaries;

      //! Equal Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> equalSummaries;

      //! Extract Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> extractSummaries;

      //! Ite Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> iteSummaries;

      //! Land Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> landSummaries;

      //! Lnot Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> lnotSummaries;

      //! Lor Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> lorSummaries;

      //! Reference Summaries
      extern std::map<triton::uint128, triton::smt2lib::smtAstAbstractNode*> referenceSummaries;

      //! String Summaries
      extern std::map<std::string, triton::smt2lib::smtAstAbstractNode*> stringSummaries;

      //! Sx Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> sxSummaries;

      //! Variable Summaries
      extern std::map<std::string, triton::smt2lib::smtAstAbstractNode*> variableSummaries;

      //! Zx Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> zxSummaries;

      //! Browses into summaries
      triton::smt2lib::smtAstAbstractNode* browseSummaries(triton::smt2lib::smtAstAbstractNode* node);

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICSUMMARY_H */

