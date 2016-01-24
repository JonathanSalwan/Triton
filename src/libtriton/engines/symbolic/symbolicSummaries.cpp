//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <symbolicSummaries.hpp>



/*
 *
 * /!\ Still experimental /!\
 *
 */
namespace triton {
  namespace engines {
    namespace symbolic {

      SymbolicSummaries::SymbolicSummaries() {
      }


      SymbolicSummaries::~SymbolicSummaries() {
      }


      triton::smt2lib::smtAstAbstractNode* SymbolicSummaries::browseSymbolicSummaries(triton::smt2lib::smtAstAbstractNode* node) {
        switch (node->getKind()) {

          case triton::smt2lib::ASSERT_NODE: {
            auto value = node->getChilds();
            if (this->assertSummaries.find(value) != this->assertSummaries.end()) {
              delete node;
              return this->assertSummaries[value];
            }
            this->assertSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVADD_NODE: {
            auto value = node->getChilds();
            if (this->bvaddSummaries.find(value) != this->bvaddSummaries.end()) {
              delete node;
              return this->bvaddSummaries[value];
            }
            this->bvaddSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVAND_NODE: {
            auto value = node->getChilds();
            if (this->bvandSummaries.find(value) != this->bvandSummaries.end()) {
              delete node;
              return this->bvandSummaries[value];
            }
            this->bvandSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVASHR_NODE: {
            auto value = node->getChilds();
            if (this->bvashrSummaries.find(value) != this->bvashrSummaries.end()) {
              delete node;
              return this->bvashrSummaries[value];
            }
            this->bvashrSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVLSHR_NODE: {
            auto value = node->getChilds();
            if (this->bvlshrSummaries.find(value) != this->bvlshrSummaries.end()) {
              delete node;
              return this->bvlshrSummaries[value];
            }
            this->bvlshrSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVMUL_NODE: {
            auto value = node->getChilds();
            if (this->bvmulSummaries.find(value) != this->bvmulSummaries.end()) {
              delete node;
              return this->bvmulSummaries[value];
            }
            this->bvmulSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVNAND_NODE: {
            auto value = node->getChilds();
            if (this->bvnandSummaries.find(value) != this->bvnandSummaries.end()) {
              delete node;
              return this->bvnandSummaries[value];
            }
            this->bvnandSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVNEG_NODE: {
            auto value = node->getChilds();
            if (this->bvnegSummaries.find(value) != this->bvnegSummaries.end()) {
              delete node;
              return this->bvnegSummaries[value];
            }
            this->bvnegSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVNOR_NODE: {
            auto value = node->getChilds();
            if (this->bvnorSummaries.find(value) != this->bvnorSummaries.end()) {
              delete node;
              return this->bvnorSummaries[value];
            }
            this->bvnorSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVNOT_NODE: {
            auto value = node->getChilds();
            if (this->bvnotSummaries.find(value) != this->bvnotSummaries.end()) {
              delete node;
              return this->bvnotSummaries[value];
            }
            this->bvnotSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVOR_NODE: {
            auto value = node->getChilds();
            if (this->bvorSummaries.find(value) != this->bvorSummaries.end()) {
              delete node;
              return this->bvorSummaries[value];
            }
            this->bvorSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVROL_NODE: {
            auto value = node->getChilds();
            if (this->bvrolSummaries.find(value) != this->bvrolSummaries.end()) {
              delete node;
              return this->bvrolSummaries[value];
            }
            this->bvrolSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVROR_NODE: {
            auto value = node->getChilds();
            if (this->bvrorSummaries.find(value) != this->bvrorSummaries.end()) {
              delete node;
              return this->bvrorSummaries[value];
            }
            this->bvrorSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVSDIV_NODE: {
            auto value = node->getChilds();
            if (this->bvsdivSummaries.find(value) != this->bvsdivSummaries.end()) {
              delete node;
              return this->bvsdivSummaries[value];
            }
            this->bvsdivSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVSGE_NODE: {
            auto value = node->getChilds();
            if (this->bvsgeSummaries.find(value) != this->bvsgeSummaries.end()) {
              delete node;
              return this->bvsgeSummaries[value];
            }
            this->bvsgeSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVSGT_NODE: {
            auto value = node->getChilds();
            if (this->bvsgtSummaries.find(value) != this->bvsgtSummaries.end()) {
              delete node;
              return this->bvsgtSummaries[value];
            }
            this->bvsgtSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVSHL_NODE: {
            auto value = node->getChilds();
            if (this->bvshlSummaries.find(value) != this->bvshlSummaries.end()) {
              delete node;
              return this->bvshlSummaries[value];
            }
            this->bvshlSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVSLE_NODE: {
            auto value = node->getChilds();
            if (this->bvsleSummaries.find(value) != this->bvsleSummaries.end()) {
              delete node;
              return this->bvsleSummaries[value];
            }
            this->bvsleSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVSLT_NODE: {
            auto value = node->getChilds();
            if (this->bvsltSummaries.find(value) != this->bvsltSummaries.end()) {
              delete node;
              return this->bvsltSummaries[value];
            }
            this->bvsltSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVSMOD_NODE: {
            auto value = node->getChilds();
            if (this->bvsmodSummaries.find(value) != this->bvsmodSummaries.end()) {
              delete node;
              return this->bvsmodSummaries[value];
            }
            this->bvsmodSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVSREM_NODE: {
            auto value = node->getChilds();
            if (this->bvsremSummaries.find(value) != this->bvsremSummaries.end()) {
              delete node;
              return this->bvsremSummaries[value];
            }
            this->bvsremSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVSUB_NODE: {
            auto value = node->getChilds();
            if (this->bvsubSummaries.find(value) != this->bvsubSummaries.end()) {
              delete node;
              return this->bvsubSummaries[value];
            }
            this->bvsubSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVUDIV_NODE: {
            auto value = node->getChilds();
            if (this->bvudivSummaries.find(value) != this->bvudivSummaries.end()) {
              delete node;
              return this->bvudivSummaries[value];
            }
            this->bvudivSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVUGE_NODE: {
            auto value = node->getChilds();
            if (this->bvugeSummaries.find(value) != this->bvugeSummaries.end()) {
              delete node;
              return this->bvugeSummaries[value];
            }
            this->bvugeSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVUGT_NODE: {
            auto value = node->getChilds();
            if (this->bvugtSummaries.find(value) != this->bvugtSummaries.end()) {
              delete node;
              return this->bvugtSummaries[value];
            }
            this->bvugtSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVULE_NODE: {
            auto value = node->getChilds();
            if (this->bvuleSummaries.find(value) != this->bvuleSummaries.end()) {
              delete node;
              return this->bvuleSummaries[value];
            }
            this->bvuleSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVULT_NODE: {
            auto value = node->getChilds();
            if (this->bvultSummaries.find(value) != this->bvultSummaries.end()) {
              delete node;
              return this->bvultSummaries[value];
            }
            this->bvultSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVUREM_NODE: {
            auto value = node->getChilds();
            if (this->bvuremSummaries.find(value) != this->bvuremSummaries.end()) {
              delete node;
              return this->bvuremSummaries[value];
            }
            this->bvuremSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVXNOR_NODE: {
            auto value = node->getChilds();
            if (this->bvxnorSummaries.find(value) != this->bvxnorSummaries.end()) {
              delete node;
              return this->bvxnorSummaries[value];
            }
            this->bvxnorSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BVXOR_NODE: {
            auto value = node->getChilds();
            if (this->bvxorSummaries.find(value) != this->bvxorSummaries.end()) {
              delete node;
              return this->bvxorSummaries[value];
            }
            this->bvxorSummaries[value] = node;
            break;
          }

          case triton::smt2lib::BV_NODE: {
            auto value = node->getChilds();
            if (this->bvSummaries.find(value) != this->bvSummaries.end()) {
              delete node;
              return this->bvSummaries[value];
            }
            this->bvSummaries[value] = node;
            break;
          }

          case triton::smt2lib::COMPOUND_NODE: {
            auto value = node->getChilds();
            if (this->compoundSummaries.find(value) != this->compoundSummaries.end()) {
              delete node;
              return this->compoundSummaries[value];
            }
            this->compoundSummaries[value] = node;
            break;
          }

          case triton::smt2lib::CONCAT_NODE: {
            auto value = node->getChilds();
            if (this->concatSummaries.find(value) != this->concatSummaries.end()) {
              delete node;
              return this->concatSummaries[value];
            }
            this->concatSummaries[value] = node;
            break;
          }

          case triton::smt2lib::DECIMAL_NODE: {
            auto value = reinterpret_cast<triton::smt2lib::smtAstDecimalNode*>(node)->getValue();
            if (this->decimalSummaries.find(value) != this->decimalSummaries.end()) {
              delete node;
              return this->decimalSummaries[value];
            }
            this->decimalSummaries[value] = node;
            break;
          }

          case triton::smt2lib::DECLARE_NODE: {
            auto value = node->getChilds();
            if (this->declareSummaries.find(value) != this->declareSummaries.end()) {
              delete node;
              return this->declareSummaries[value];
            }
            this->declareSummaries[value] = node;
            break;
          }

          case triton::smt2lib::DISTINCT_NODE: {
            auto value = node->getChilds();
            if (this->distinctSummaries.find(value) != this->distinctSummaries.end()) {
              delete node;
              return this->distinctSummaries[value];
            }
            this->distinctSummaries[value] = node;
            break;
          }

          case triton::smt2lib::EQUAL_NODE: {
            auto value = node->getChilds();
            if (this->equalSummaries.find(value) != this->equalSummaries.end()) {
              delete node;
              return this->equalSummaries[value];
            }
            this->equalSummaries[value] = node;
            break;
          }

          case triton::smt2lib::EXTRACT_NODE: {
            auto value = node->getChilds();
            if (this->extractSummaries.find(value) != this->extractSummaries.end()) {
              delete node;
              return this->extractSummaries[value];
            }
            this->extractSummaries[value] = node;
            break;
          }

          case triton::smt2lib::ITE_NODE: {
            auto value = node->getChilds();
            if (this->iteSummaries.find(value) != this->iteSummaries.end()) {
              delete node;
              return this->iteSummaries[value];
            }
            this->iteSummaries[value] = node;
            break;
          }

          case triton::smt2lib::LAND_NODE: {
            auto value = node->getChilds();
            if (this->landSummaries.find(value) != this->landSummaries.end()) {
              delete node;
              return this->landSummaries[value];
            }
            this->landSummaries[value] = node;
            break;
          }

          case triton::smt2lib::LNOT_NODE: {
            auto value = node->getChilds();
            if (this->lnotSummaries.find(value) != this->lnotSummaries.end()) {
              delete node;
              return this->lnotSummaries[value];
            }
            this->lnotSummaries[value] = node;
            break;
          }

          case triton::smt2lib::LOR_NODE: {
            auto value = node->getChilds();
            if (this->lorSummaries.find(value) != this->lorSummaries.end()) {
              delete node;
              return this->lorSummaries[value];
            }
            this->lorSummaries[value] = node;
            break;
          }

          case triton::smt2lib::REFERENCE_NODE: {
            auto value = reinterpret_cast<triton::smt2lib::smtAstReferenceNode*>(node)->getValue();
            if (this->referenceSummaries.find(value) != this->referenceSummaries.end()) {
              delete node;
              return this->referenceSummaries[value];
            }
            this->referenceSummaries[value] = node;
            break;
          }

          case triton::smt2lib::STRING_NODE: {
            auto value = reinterpret_cast<triton::smt2lib::smtAstStringNode*>(node)->getValue();
            if (this->stringSummaries.find(value) != this->stringSummaries.end()) {
              delete node;
              return this->stringSummaries[value];
            }
            this->stringSummaries[value] = node;
            break;
          }

          case triton::smt2lib::SX_NODE: {
            auto value = node->getChilds();
            if (this->sxSummaries.find(value) != this->sxSummaries.end()) {
              delete node;
              return this->sxSummaries[value];
            }
            this->sxSummaries[value] = node;
            break;
          }

          case triton::smt2lib::VARIABLE_NODE: {
            auto value = reinterpret_cast<triton::smt2lib::smtAstVariableNode*>(node)->getValue();
            if (this->variableSummaries.find(value) != this->variableSummaries.end()) {
              delete node;
              return this->variableSummaries[value];
            }
            this->variableSummaries[value] = node;
            break;
          }

          case triton::smt2lib::ZX_NODE: {
            auto value = node->getChilds();
            if (this->zxSummaries.find(value) != this->zxSummaries.end()) {
              delete node;
              return this->zxSummaries[value];
            }
            this->zxSummaries[value] = node;
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

