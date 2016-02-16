//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SYMBOLICSUMMARIE_H
#define TRITON_SYMBOLICSUMMARIE_H

#include <list>

#include "ast.hpp"
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
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> assertSummaries;

          //! Bvadd Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvaddSummaries;

          //! Bvand Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvandSummaries;

          //! Bvashr Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvashrSummaries;

          //! Bvdecl Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvdeclSummaries;

          //! Bvlshr Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvlshrSummaries;

          //! Bvmul Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvmulSummaries;

          //! Bvnand Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvnandSummaries;

          //! Bvneg Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvnegSummaries;

          //! Bvnor Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvnorSummaries;

          //! Bvnot Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvnotSummaries;

          //! Bvor Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvorSummaries;

          //! Bvrol Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvrolSummaries;

          //! Bvror Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvrorSummaries;

          //! Bvsdiv Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvsdivSummaries;

          //! Bvsge Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvsgeSummaries;

          //! Bvsgt Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvsgtSummaries;

          //! Bvshl Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvshlSummaries;

          //! Bvsle Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvsleSummaries;

          //! Bvslt Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvsltSummaries;

          //! Bvsmod Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvsmodSummaries;

          //! Bvsrem Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvsremSummaries;

          //! Bvsub Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvsubSummaries;

          //! Bvudiv Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvudivSummaries;

          //! Bvuge Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvugeSummaries;

          //! Bvugt Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvugtSummaries;

          //! Bvule Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvuleSummaries;

          //! Bvult Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvultSummaries;

          //! Bvurem Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvuremSummaries;

          //! Bvxnor Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvxnorSummaries;

          //! Bvxor Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvxorSummaries;

          //! Bv Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> bvSummaries;

          //! Compound Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> compoundSummaries;

          //! Concat Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> concatSummaries;

          //! Decimal Summaries
          std::map<triton::uint128, triton::ast::smtAstAbstractNode*> decimalSummaries;

          //! Declare Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> declareFunctionSummaries;

          //! Distinct Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> distinctSummaries;

          //! Equal Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> equalSummaries;

          //! Extract Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> extractSummaries;

          //! Ite Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> iteSummaries;

          //! Land Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> landSummaries;

          //! Let Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> letSummaries;

          //! Lnot Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> lnotSummaries;

          //! Lor Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> lorSummaries;

          //! Reference Summaries
          std::map<triton::uint128, triton::ast::smtAstAbstractNode*> referenceSummaries;

          //! String Summaries
          std::map<std::string, triton::ast::smtAstAbstractNode*> stringSummaries;

          //! Sx Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> sxSummaries;

          //! Variable Summaries
          std::map<std::string, triton::ast::smtAstAbstractNode*> variableSummaries;

          //! Zx Summaries
          std::map<std::vector<triton::ast::smtAstAbstractNode*>, triton::ast::smtAstAbstractNode*> zxSummaries;

          //! Summaries
          std::map<triton::uint32, void*> summaries;

      public:
          //! Constructor.
          AstSummaries();

          //! Destructor.
          ~AstSummaries();

          //! Browses into summaries.
          triton::ast::smtAstAbstractNode* browseAstSummaries(triton::ast::smtAstAbstractNode* node);

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

