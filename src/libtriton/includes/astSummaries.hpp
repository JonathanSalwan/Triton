//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SYMBOLICSUMMARIE_H
#define TRITON_SYMBOLICSUMMARIE_H

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

      //! \class AstSummaries
      /*! \brief The AST summaries class */
      class AstSummaries {

        protected:
          //! Total of allocated nodes.
          triton::uint32 allocatedNodes;

          //! Total of allocated summaries.
          triton::uint32 allocatedSummaries;

          //! Assert Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> assertSummaries;

          //! Bvadd Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvaddSummaries;

          //! Bvand Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvandSummaries;

          //! Bvashr Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvashrSummaries;

          //! Bvlshr Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvlshrSummaries;

          //! Bvmul Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvmulSummaries;

          //! Bvnand Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvnandSummaries;

          //! Bvneg Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvnegSummaries;

          //! Bvnor Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvnorSummaries;

          //! Bvnot Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvnotSummaries;

          //! Bvor Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvorSummaries;

          //! Bvrol Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvrolSummaries;

          //! Bvror Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvrorSummaries;

          //! Bvsdiv Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsdivSummaries;

          //! Bvsge Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsgeSummaries;

          //! Bvsgt Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsgtSummaries;

          //! Bvshl Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvshlSummaries;

          //! Bvsle Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsleSummaries;

          //! Bvslt Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsltSummaries;

          //! Bvsmod Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsmodSummaries;

          //! Bvsrem Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsremSummaries;

          //! Bvsub Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsubSummaries;

          //! Bvudiv Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvudivSummaries;

          //! Bvuge Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvugeSummaries;

          //! Bvugt Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvugtSummaries;

          //! Bvule Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvuleSummaries;

          //! Bvult Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvultSummaries;

          //! Bvurem Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvuremSummaries;

          //! Bvxnor Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvxnorSummaries;

          //! Bvxor Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvxorSummaries;

          //! Bv Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvSummaries;

          //! Compound Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> compoundSummaries;

          //! Concat Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> concatSummaries;

          //! Decimal Summaries
          std::map<triton::uint128, triton::smt2lib::smtAstAbstractNode*> decimalSummaries;

          //! Declare Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> declareSummaries;

          //! Distinct Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> distinctSummaries;

          //! Equal Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> equalSummaries;

          //! Extract Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> extractSummaries;

          //! Ite Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> iteSummaries;

          //! Land Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> landSummaries;

          //! Lnot Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> lnotSummaries;

          //! Lor Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> lorSummaries;

          //! Reference Summaries
          std::map<triton::uint128, triton::smt2lib::smtAstAbstractNode*> referenceSummaries;

          //! String Summaries
          std::map<std::string, triton::smt2lib::smtAstAbstractNode*> stringSummaries;

          //! Sx Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> sxSummaries;

          //! Variable Summaries
          std::map<std::string, triton::smt2lib::smtAstAbstractNode*> variableSummaries;

          //! Zx Summaries
          std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> zxSummaries;

          //! Summaries
          std::map<triton::uint32, void*> summaries;

      public:
          //! Constructor.
          AstSummaries();

          //! Destructor.
          ~AstSummaries();

          //! Browses into summaries.
          triton::smt2lib::smtAstAbstractNode* browseAstSummaries(triton::smt2lib::smtAstAbstractNode* node);

          //! Returns stats about summaries.
          std::map<std::string, triton::uint32> getAstSummariesStats(void);
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICSUMMARIE_H */

