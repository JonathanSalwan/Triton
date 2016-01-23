//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <symbolicSummary.hpp>



/*
 *
 * /!\ Still experimental /!\
 *
 */
namespace triton {
  namespace engines {
    namespace symbolic {

      /* Assert Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> assertSummaries;

      /* Bvadd Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvaddSummaries;

      /* Bvand Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvandSummaries;

      /* Bvashr Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvashrSummaries;

      /* Bvlshr Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvlshrSummaries;

      /* Bvmul Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvmulSummaries;

      /* Bvnand Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvnandSummaries;

      /* Bvneg Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvnegSummaries;

      /* Bvnor Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvnorSummaries;

      /* Bvnot Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvnotSummaries;

      /* Bvor Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvorSummaries;

      /* Bvrol Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvrolSummaries;

      /* Bvror Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvrorSummaries;

      /* Bvsdiv Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsdivSummariaes;

      /* Bvsge Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsgeSummaries;

      /* Bvsgt Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsgtSummaries;

      /* Bvshl Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvshlSummaries;

      /* Bvsle Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsleSummaries;

      /* Bvslt Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsltSummaries;

      /* Bvsmod Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsmodSummaries;

      /* Bvsrem Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsremSummaries;

      /* Bvsub Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvsubSummaries;

      /* Bvudiv Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvudivSummaries;

      /* Bvuge Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvugeSummaries;

      /* Bvugt Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvugtSummaries;

      /* Bvule Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvuleSummaries;

      /* Bvult Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvultSummaries;

      /* Bvurem Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvuremSummaries;

      /* Bvxnor Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvxnorSummaries;

      /* Bvxor Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvxorSummaries;

      /* Bv Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvSummaries;

      /* Compound Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> compoundSummaries;

      /* Concat Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> concatSummaries;

      /* Decimal Summaries */
      std::map<triton::uint128, triton::smt2lib::smtAstAbstractNode*> decimalSummaries;

      /* Declare Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> declareSummaries;

      /* Distinct Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> distinctSummaries;

      /* Equal Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> equalSummaries;

      /* Extract Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> extractSummaries;

      /* Ite Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> iteSummaries;

      /* Land Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> landSummaries;

      /* Lnot Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> lnotSummaries;

      /* Lor Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> lorSummaries;

      /* Reference Summaries */
      std::map<triton::uint128, triton::smt2lib::smtAstAbstractNode*> referenceSummaries;

      /* String Summaries */
      std::map<std::string, triton::smt2lib::smtAstAbstractNode*> stringSummaries;

      /* Sx Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> sxSummaries;

      /* Variable Summaries */
      std::map<std::string, triton::smt2lib::smtAstAbstractNode*> variableSummaries;

      /* Zx Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> zxSummaries;


      /* Browses into summaries */
      triton::smt2lib::smtAstAbstractNode* browseSummaries(triton::smt2lib::smtAstAbstractNode* node) {
        switch (node->getKind()) {

          //case triton::smt2lib::ASSERT_NODE:
          //case triton::smt2lib::BVADD_NODE:
          //case triton::smt2lib::BVAND_NODE:
          //case triton::smt2lib::BVASHR_NODE:
          //case triton::smt2lib::BVLSHR_NODE:
          //case triton::smt2lib::BVMUL_NODE:
          //case triton::smt2lib::BVNAND_NODE:
          //case triton::smt2lib::BVNEG_NODE:
          //case triton::smt2lib::BVNOR_NODE:
          //case triton::smt2lib::BVNOT_NODE:
          //case triton::smt2lib::BVOR_NODE:
          //case triton::smt2lib::BVROL_NODE:
          //case triton::smt2lib::BVROR_NODE:
          //case triton::smt2lib::BVSDIV_NODE:
          //case triton::smt2lib::BVSGE_NODE:
          //case triton::smt2lib::BVSGT_NODE:
          //case triton::smt2lib::BVSHL_NODE:
          //case triton::smt2lib::BVSLE_NODE:
          //case triton::smt2lib::BVSLT_NODE:
          //case triton::smt2lib::BVSMOD_NODE:
          //case triton::smt2lib::BVSREM_NODE:
          //case triton::smt2lib::BVSUB_NODE:
          //case triton::smt2lib::BVUDIV_NODE:
          //case triton::smt2lib::BVUGE_NODE:
          //case triton::smt2lib::BVUGT_NODE:
          //case triton::smt2lib::BVULE_NODE:
          //case triton::smt2lib::BVULT_NODE:
          //case triton::smt2lib::BVUREM_NODE:
          //case triton::smt2lib::BVXNOR_NODE:
          //case triton::smt2lib::BVXOR_NODE:

          case triton::smt2lib::BV_NODE: {
            auto value = node->getChilds();
            if (bvSummaries.find(value) != bvSummaries.end()) {
              delete node;
              return bvSummaries[value];
            }
            bvSummaries[value] = node;
            break;
          }

          //case triton::smt2lib::COMPOUND_NODE:
          //case triton::smt2lib::CONCAT_NODE:

          case triton::smt2lib::DECIMAL_NODE: {
            auto value = reinterpret_cast<triton::smt2lib::smtAstDecimalNode*>(node)->getValue();
            if (decimalSummaries.find(value) != decimalSummaries.end()) {
              delete node;
              return decimalSummaries[value];
            }
            decimalSummaries[value] = node;
            break;
          }

          //case triton::smt2lib::DECLARE_NODE:
          //case triton::smt2lib::DISTINCT_NODE:
          //case triton::smt2lib::EQUAL_NODE:
          //case triton::smt2lib::EXTRACT_NODE:
          //case triton::smt2lib::ITE_NODE:
          //case triton::smt2lib::LAND_NODE:
          //case triton::smt2lib::LNOT_NODE:
          //case triton::smt2lib::LOR_NODE:
          //case triton::smt2lib::REFERENCE_NODE:
          //case triton::smt2lib::STRING_NODE:
          //case triton::smt2lib::SX_NODE:
          //case triton::smt2lib::VARIABLE_NODE:
          //case triton::smt2lib::ZX_NODE:

          default:
            break;
        }
        return nullptr;
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

