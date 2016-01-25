//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <astSummaries.hpp>



namespace triton {
  namespace engines {
    namespace symbolic {

      AstSummaries::AstSummaries() {
        this->allocatedNodes     = 0;
        this->allocatedSummaries = 0;

        this->summaries[triton::smt2lib::ASSERT_NODE]     = &this->assertSummaries;
        this->summaries[triton::smt2lib::BVADD_NODE]      = &this->bvaddSummaries;
        this->summaries[triton::smt2lib::BVAND_NODE]      = &this->bvandSummaries;
        this->summaries[triton::smt2lib::BVASHR_NODE]     = &this->bvashrSummaries;
        this->summaries[triton::smt2lib::BVLSHR_NODE]     = &this->bvlshrSummaries;
        this->summaries[triton::smt2lib::BVMUL_NODE]      = &this->bvmulSummaries;
        this->summaries[triton::smt2lib::BVNAND_NODE]     = &this->bvnandSummaries;
        this->summaries[triton::smt2lib::BVNEG_NODE]      = &this->bvnegSummaries;
        this->summaries[triton::smt2lib::BVNOR_NODE]      = &this->bvnorSummaries;
        this->summaries[triton::smt2lib::BVNOT_NODE]      = &this->bvnotSummaries;
        this->summaries[triton::smt2lib::BVOR_NODE]       = &this->bvorSummaries;
        this->summaries[triton::smt2lib::BVROL_NODE]      = &this->bvrolSummaries;
        this->summaries[triton::smt2lib::BVROR_NODE]      = &this->bvrorSummaries;
        this->summaries[triton::smt2lib::BVSDIV_NODE]     = &this->bvsdivSummaries;
        this->summaries[triton::smt2lib::BVSGE_NODE]      = &this->bvsgeSummaries;
        this->summaries[triton::smt2lib::BVSGT_NODE]      = &this->bvsgtSummaries;
        this->summaries[triton::smt2lib::BVSHL_NODE]      = &this->bvshlSummaries;
        this->summaries[triton::smt2lib::BVSLE_NODE]      = &this->bvsleSummaries;
        this->summaries[triton::smt2lib::BVSLT_NODE]      = &this->bvsltSummaries;
        this->summaries[triton::smt2lib::BVSMOD_NODE]     = &this->bvsmodSummaries;
        this->summaries[triton::smt2lib::BVSREM_NODE]     = &this->bvsremSummaries;
        this->summaries[triton::smt2lib::BVSUB_NODE]      = &this->bvsubSummaries;
        this->summaries[triton::smt2lib::BVUDIV_NODE]     = &this->bvudivSummaries;
        this->summaries[triton::smt2lib::BVUGE_NODE]      = &this->bvugeSummaries;
        this->summaries[triton::smt2lib::BVUGT_NODE]      = &this->bvugtSummaries;
        this->summaries[triton::smt2lib::BVULE_NODE]      = &this->bvuleSummaries;
        this->summaries[triton::smt2lib::BVULT_NODE]      = &this->bvultSummaries;
        this->summaries[triton::smt2lib::BVUREM_NODE]     = &this->bvuremSummaries;
        this->summaries[triton::smt2lib::BVXNOR_NODE]     = &this->bvxnorSummaries;
        this->summaries[triton::smt2lib::BVXOR_NODE]      = &this->bvxorSummaries;
        this->summaries[triton::smt2lib::BV_NODE]         = &this->bvSummaries;
        this->summaries[triton::smt2lib::COMPOUND_NODE]   = &this->compoundSummaries;
        this->summaries[triton::smt2lib::CONCAT_NODE]     = &this->concatSummaries;
        this->summaries[triton::smt2lib::DECIMAL_NODE]    = &this->decimalSummaries;
        this->summaries[triton::smt2lib::DECLARE_NODE]    = &this->declareSummaries;
        this->summaries[triton::smt2lib::DISTINCT_NODE]   = &this->distinctSummaries;
        this->summaries[triton::smt2lib::EQUAL_NODE]      = &this->equalSummaries;
        this->summaries[triton::smt2lib::EXTRACT_NODE]    = &this->extractSummaries;
        this->summaries[triton::smt2lib::ITE_NODE]        = &this->iteSummaries;
        this->summaries[triton::smt2lib::LAND_NODE]       = &this->landSummaries;
        this->summaries[triton::smt2lib::LNOT_NODE]       = &this->lnotSummaries;
        this->summaries[triton::smt2lib::LOR_NODE]        = &this->lorSummaries;
        this->summaries[triton::smt2lib::REFERENCE_NODE]  = &this->referenceSummaries;
        this->summaries[triton::smt2lib::STRING_NODE]     = &this->stringSummaries;
        this->summaries[triton::smt2lib::SX_NODE]         = &this->sxSummaries;
        this->summaries[triton::smt2lib::VARIABLE_NODE]   = &this->variableSummaries;
        this->summaries[triton::smt2lib::ZX_NODE]         = &this->zxSummaries;
      }


      AstSummaries::~AstSummaries() {
      }


      triton::smt2lib::smtAstAbstractNode* AstSummaries::browseAstSummaries(triton::smt2lib::smtAstAbstractNode* node) {
        this->allocatedNodes++;
        triton::uint32 kind = node->getKind();

        switch (kind) {

          case triton::smt2lib::DECIMAL_NODE: {
            auto value      = reinterpret_cast<triton::smt2lib::smtAstDecimalNode*>(node)->getValue();
            auto summaries  = static_cast<std::map<triton::uint128, triton::smt2lib::smtAstAbstractNode*>*>((this->summaries[kind]));
            if (summaries->find(value) != summaries->end()) {
              delete node;
              return (*summaries)[value];
            }
            (*summaries)[value] = node;
            break;
          }

          case triton::smt2lib::REFERENCE_NODE: {
            auto value      = reinterpret_cast<triton::smt2lib::smtAstReferenceNode*>(node)->getValue();
            auto summaries  = static_cast<std::map<triton::uint128, triton::smt2lib::smtAstAbstractNode*>*>((this->summaries[kind]));
            if (summaries->find(value) != summaries->end()) {
              delete node;
              return (*summaries)[value];
            }
            (*summaries)[value] = node;
            break;
          }

          case triton::smt2lib::STRING_NODE: {
            auto value      = reinterpret_cast<triton::smt2lib::smtAstStringNode*>(node)->getValue();
            auto summaries  = static_cast<std::map<std::string, triton::smt2lib::smtAstAbstractNode*>*>((this->summaries[kind]));
            if (summaries->find(value) != summaries->end()) {
              delete node;
              return (*summaries)[value];
            }
            (*summaries)[value] = node;
            break;
          }

          case triton::smt2lib::VARIABLE_NODE: {
            auto value      = reinterpret_cast<triton::smt2lib::smtAstVariableNode*>(node)->getValue();
            auto summaries  = static_cast<std::map<std::string, triton::smt2lib::smtAstAbstractNode*>*>((this->summaries[kind]));
            if (summaries->find(value) != summaries->end()) {
              delete node;
              return (*summaries)[value];
            }
            (*summaries)[value] = node;
            break;
          }

          default: {
            auto value      = node->getChilds();
            auto summaries  = static_cast<std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*>*>((this->summaries[kind]));
            if (summaries->find(value) != summaries->end()) {
              delete node;
              return (*summaries)[value];
            }
            (*summaries)[value] = node;
            break;
          }

        }

        this->allocatedSummaries++;
        return nullptr;
      }


      std::map<std::string, triton::uint32> AstSummaries::getAstSummariesStats(void) {
        std::map<std::string, triton::uint32> stats;
        stats["assert"]             = this->assertSummaries.size();
        stats["bvadd"]              = this->bvaddSummaries.size();
        stats["bvand"]              = this->bvandSummaries.size();
        stats["bvashr"]             = this->bvashrSummaries.size();
        stats["bvlshr"]             = this->bvlshrSummaries.size();
        stats["bvmul"]              = this->bvmulSummaries.size();
        stats["bvnand"]             = this->bvnandSummaries.size();
        stats["bvneg"]              = this->bvnegSummaries.size();
        stats["bvnor"]              = this->bvnorSummaries.size();
        stats["bvnot"]              = this->bvnotSummaries.size();
        stats["bvor"]               = this->bvorSummaries.size();
        stats["bvrol"]              = this->bvrolSummaries.size();
        stats["bvror"]              = this->bvrorSummaries.size();
        stats["bvsdiv"]             = this->bvsdivSummaries.size();
        stats["bvsge"]              = this->bvsgeSummaries.size();
        stats["bvsgt"]              = this->bvsgtSummaries.size();
        stats["bvshl"]              = this->bvshlSummaries.size();
        stats["bvsle"]              = this->bvsleSummaries.size();
        stats["bvslt"]              = this->bvsltSummaries.size();
        stats["bvsmod"]             = this->bvsmodSummaries.size();
        stats["bvsrem"]             = this->bvsremSummaries.size();
        stats["bvsub"]              = this->bvsubSummaries.size();
        stats["bvudiv"]             = this->bvudivSummaries.size();
        stats["bvuge"]              = this->bvugeSummaries.size();
        stats["bvugt"]              = this->bvugtSummaries.size();
        stats["bvule"]              = this->bvuleSummaries.size();
        stats["bvult"]              = this->bvultSummaries.size();
        stats["bvurem"]             = this->bvuremSummaries.size();
        stats["bvxnor"]             = this->bvxnorSummaries.size();
        stats["bvxor"]              = this->bvxorSummaries.size();
        stats["bv"]                 = this->bvSummaries.size();
        stats["compound"]           = this->compoundSummaries.size();
        stats["concat"]             = this->concatSummaries.size();
        stats["decimal"]            = this->decimalSummaries.size();
        stats["declare"]            = this->declareSummaries.size();
        stats["distinct"]           = this->distinctSummaries.size();
        stats["equal"]              = this->equalSummaries.size();
        stats["extract"]            = this->extractSummaries.size();
        stats["ite"]                = this->iteSummaries.size();
        stats["land"]               = this->landSummaries.size();
        stats["lnot"]               = this->lnotSummaries.size();
        stats["lor"]                = this->lorSummaries.size();
        stats["reference"]          = this->referenceSummaries.size();
        stats["string"]             = this->stringSummaries.size();
        stats["sx"]                 = this->sxSummaries.size();
        stats["variable"]           = this->variableSummaries.size();
        stats["zx"]                 = this->zxSummaries.size();
        stats["allocatedSummaries"] = this->allocatedSummaries;
        stats["allocatedNodes"]     = this->allocatedNodes;
        return stats;
      }


    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

