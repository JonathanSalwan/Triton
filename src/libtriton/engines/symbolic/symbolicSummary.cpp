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

      /* Decimal Summaries */
      std::map<triton::uint128, triton::smt2lib::smtAstAbstractNode*> decimalSummaries;

      /* Bv Summaries */
      std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvSummaries;

      /* Browses into summaries */
      triton::smt2lib::smtAstAbstractNode* browseSummaries(triton::smt2lib::smtAstAbstractNode* node) {
        switch (node->getKind()) {

          case triton::smt2lib::BV_NODE: {
            auto value = node->getChilds();
            if (bvSummaries.find(value) != bvSummaries.end()) {
              delete node;
              return bvSummaries[value];
            }
            bvSummaries[value] = node;
            break;
          }

          case triton::smt2lib::DECIMAL_NODE: {
            auto value = reinterpret_cast<triton::smt2lib::smtAstDecimalNode*>(node)->getValue();
            if (decimalSummaries.find(value) != decimalSummaries.end()) {
              delete node;
              return decimalSummaries[value];
            }
            decimalSummaries[value] = node;
            break;
          }

          default:
            break;
        }
        return nullptr;
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

