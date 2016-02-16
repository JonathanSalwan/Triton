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
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> assertSummaries;

          //! Bvadd Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvaddSummaries;

          //! Bvand Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvandSummaries;

          //! Bvashr Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvashrSummaries;

          //! Bvdecl Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvdeclSummaries;

          //! Bvlshr Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvlshrSummaries;

          //! Bvmul Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvmulSummaries;

          //! Bvnand Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvnandSummaries;

          //! Bvneg Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvnegSummaries;

          //! Bvnor Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvnorSummaries;

          //! Bvnot Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvnotSummaries;

          //! Bvor Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvorSummaries;

          //! Bvrol Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvrolSummaries;

          //! Bvror Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvrorSummaries;

          //! Bvsdiv Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvsdivSummaries;

          //! Bvsge Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvsgeSummaries;

          //! Bvsgt Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvsgtSummaries;

          //! Bvshl Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvshlSummaries;

          //! Bvsle Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvsleSummaries;

          //! Bvslt Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvsltSummaries;

          //! Bvsmod Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvsmodSummaries;

          //! Bvsrem Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvsremSummaries;

          //! Bvsub Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvsubSummaries;

          //! Bvudiv Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvudivSummaries;

          //! Bvuge Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvugeSummaries;

          //! Bvugt Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvugtSummaries;

          //! Bvule Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvuleSummaries;

          //! Bvult Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvultSummaries;

          //! Bvurem Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvuremSummaries;

          //! Bvxnor Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvxnorSummaries;

          //! Bvxor Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvxorSummaries;

          //! Bv Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvSummaries;

          //! Compound Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> compoundSummaries;

          //! Concat Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> concatSummaries;

          //! Decimal Summaries
          std::map<triton::uint128, triton::ast::AbstractNode*> decimalSummaries;

          //! Declare Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> declareFunctionSummaries;

          //! Distinct Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> distinctSummaries;

          //! Equal Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> equalSummaries;

          //! Extract Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> extractSummaries;

          //! Ite Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> iteSummaries;

          //! Land Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> landSummaries;

          //! Let Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> letSummaries;

          //! Lnot Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> lnotSummaries;

          //! Lor Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> lorSummaries;

          //! Reference Summaries
          std::map<triton::uint128, triton::ast::AbstractNode*> referenceSummaries;

          //! String Summaries
          std::map<std::string, triton::ast::AbstractNode*> stringSummaries;

          //! Sx Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> sxSummaries;

          //! Variable Summaries
          std::map<std::string, triton::ast::AbstractNode*> variableSummaries;

          //! Zx Summaries
          std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> zxSummaries;

          //! Summaries
          std::map<triton::uint32, void*> summaries;

      public:
          //! Constructor.
          AstSummaries();

          //! Destructor.
          ~AstSummaries();

          //! Browses into summaries.
          triton::ast::AbstractNode* browseAstSummaries(triton::ast::AbstractNode* node);

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

