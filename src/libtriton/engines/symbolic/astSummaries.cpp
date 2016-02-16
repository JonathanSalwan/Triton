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

        this->summaries[triton::ast::ASSERT_NODE]             = &this->assertSummaries;
        this->summaries[triton::ast::BVADD_NODE]              = &this->bvaddSummaries;
        this->summaries[triton::ast::BVAND_NODE]              = &this->bvandSummaries;
        this->summaries[triton::ast::BVASHR_NODE]             = &this->bvashrSummaries;
        this->summaries[triton::ast::BVDECL_NODE]             = &this->bvdeclSummaries;
        this->summaries[triton::ast::BVLSHR_NODE]             = &this->bvlshrSummaries;
        this->summaries[triton::ast::BVMUL_NODE]              = &this->bvmulSummaries;
        this->summaries[triton::ast::BVNAND_NODE]             = &this->bvnandSummaries;
        this->summaries[triton::ast::BVNEG_NODE]              = &this->bvnegSummaries;
        this->summaries[triton::ast::BVNOR_NODE]              = &this->bvnorSummaries;
        this->summaries[triton::ast::BVNOT_NODE]              = &this->bvnotSummaries;
        this->summaries[triton::ast::BVOR_NODE]               = &this->bvorSummaries;
        this->summaries[triton::ast::BVROL_NODE]              = &this->bvrolSummaries;
        this->summaries[triton::ast::BVROR_NODE]              = &this->bvrorSummaries;
        this->summaries[triton::ast::BVSDIV_NODE]             = &this->bvsdivSummaries;
        this->summaries[triton::ast::BVSGE_NODE]              = &this->bvsgeSummaries;
        this->summaries[triton::ast::BVSGT_NODE]              = &this->bvsgtSummaries;
        this->summaries[triton::ast::BVSHL_NODE]              = &this->bvshlSummaries;
        this->summaries[triton::ast::BVSLE_NODE]              = &this->bvsleSummaries;
        this->summaries[triton::ast::BVSLT_NODE]              = &this->bvsltSummaries;
        this->summaries[triton::ast::BVSMOD_NODE]             = &this->bvsmodSummaries;
        this->summaries[triton::ast::BVSREM_NODE]             = &this->bvsremSummaries;
        this->summaries[triton::ast::BVSUB_NODE]              = &this->bvsubSummaries;
        this->summaries[triton::ast::BVUDIV_NODE]             = &this->bvudivSummaries;
        this->summaries[triton::ast::BVUGE_NODE]              = &this->bvugeSummaries;
        this->summaries[triton::ast::BVUGT_NODE]              = &this->bvugtSummaries;
        this->summaries[triton::ast::BVULE_NODE]              = &this->bvuleSummaries;
        this->summaries[triton::ast::BVULT_NODE]              = &this->bvultSummaries;
        this->summaries[triton::ast::BVUREM_NODE]             = &this->bvuremSummaries;
        this->summaries[triton::ast::BVXNOR_NODE]             = &this->bvxnorSummaries;
        this->summaries[triton::ast::BVXOR_NODE]              = &this->bvxorSummaries;
        this->summaries[triton::ast::BV_NODE]                 = &this->bvSummaries;
        this->summaries[triton::ast::COMPOUND_NODE]           = &this->compoundSummaries;
        this->summaries[triton::ast::CONCAT_NODE]             = &this->concatSummaries;
        this->summaries[triton::ast::DECIMAL_NODE]            = &this->decimalSummaries;
        this->summaries[triton::ast::DECLARE_FUNCTION_NODE]   = &this->declareFunctionSummaries;
        this->summaries[triton::ast::DISTINCT_NODE]           = &this->distinctSummaries;
        this->summaries[triton::ast::EQUAL_NODE]              = &this->equalSummaries;
        this->summaries[triton::ast::EXTRACT_NODE]            = &this->extractSummaries;
        this->summaries[triton::ast::ITE_NODE]                = &this->iteSummaries;
        this->summaries[triton::ast::LAND_NODE]               = &this->landSummaries;
        this->summaries[triton::ast::LET_NODE]                = &this->letSummaries;
        this->summaries[triton::ast::LNOT_NODE]               = &this->lnotSummaries;
        this->summaries[triton::ast::LOR_NODE]                = &this->lorSummaries;
        this->summaries[triton::ast::REFERENCE_NODE]          = &this->referenceSummaries;
        this->summaries[triton::ast::STRING_NODE]             = &this->stringSummaries;
        this->summaries[triton::ast::SX_NODE]                 = &this->sxSummaries;
        this->summaries[triton::ast::VARIABLE_NODE]           = &this->variableSummaries;
        this->summaries[triton::ast::ZX_NODE]                 = &this->zxSummaries;
      }


      AstSummaries::~AstSummaries() {
        for (auto it = this->assertSummaries.begin(); it != this->assertSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvaddSummaries.begin(); it != this->bvaddSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvandSummaries.begin(); it != this->bvandSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvashrSummaries.begin(); it != this->bvashrSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvdeclSummaries.begin(); it != this->bvdeclSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvlshrSummaries.begin(); it != this->bvlshrSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvmulSummaries.begin(); it != this->bvmulSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvnandSummaries.begin(); it != this->bvnandSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvnegSummaries.begin(); it != this->bvnegSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvnorSummaries.begin(); it != this->bvnorSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvnotSummaries.begin(); it != this->bvnotSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvorSummaries.begin(); it != this->bvorSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvrolSummaries.begin(); it != this->bvrolSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvrorSummaries.begin(); it != this->bvrorSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvsdivSummaries.begin(); it != this->bvsdivSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvsgeSummaries.begin(); it != this->bvsgeSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvsgtSummaries.begin(); it != this->bvsgtSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvshlSummaries.begin(); it != this->bvshlSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvsleSummaries.begin(); it != this->bvsleSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvsltSummaries.begin(); it != this->bvsltSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvsmodSummaries.begin(); it != this->bvsmodSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvsremSummaries.begin(); it != this->bvsremSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvsubSummaries.begin(); it != this->bvsubSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvudivSummaries.begin(); it != this->bvudivSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvugeSummaries.begin(); it != this->bvugeSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvugtSummaries.begin(); it != this->bvugtSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvuleSummaries.begin(); it != this->bvuleSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvultSummaries.begin(); it != this->bvultSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvuremSummaries.begin(); it != this->bvuremSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvxnorSummaries.begin(); it != this->bvxnorSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvxorSummaries.begin(); it != this->bvxorSummaries.end(); it++)
          delete it->second;
        for (auto it = this->bvSummaries.begin(); it != this->bvSummaries.end(); it++)
          delete it->second;
        for (auto it = this->compoundSummaries.begin(); it != this->compoundSummaries.end(); it++)
          delete it->second;
        for (auto it = this->concatSummaries.begin(); it != this->concatSummaries.end(); it++)
          delete it->second;
        for (auto it = this->decimalSummaries.begin(); it != this->decimalSummaries.end(); it++)
          delete it->second;
        for (auto it = this->declareFunctionSummaries.begin(); it != this->declareFunctionSummaries.end(); it++)
          delete it->second;
        for (auto it = this->distinctSummaries.begin(); it != this->distinctSummaries.end(); it++)
          delete it->second;
        for (auto it = this->equalSummaries.begin(); it != this->equalSummaries.end(); it++)
          delete it->second;
        for (auto it = this->extractSummaries.begin(); it != this->extractSummaries.end(); it++)
          delete it->second;
        for (auto it = this->iteSummaries.begin(); it != this->iteSummaries.end(); it++)
          delete it->second;
        for (auto it = this->landSummaries.begin(); it != this->landSummaries.end(); it++)
          delete it->second;
        for (auto it = this->letSummaries.begin(); it != this->letSummaries.end(); it++)
          delete it->second;
        for (auto it = this->lnotSummaries.begin(); it != this->lnotSummaries.end(); it++)
          delete it->second;
        for (auto it = this->lorSummaries.begin(); it != this->lorSummaries.end(); it++)
          delete it->second;
        for (auto it = this->referenceSummaries.begin(); it != this->referenceSummaries.end(); it++)
          delete it->second;
        for (auto it = this->stringSummaries.begin(); it != this->stringSummaries.end(); it++)
          delete it->second;
        for (auto it = this->sxSummaries.begin(); it != this->sxSummaries.end(); it++)
          delete it->second;
        for (auto it = this->variableSummaries.begin(); it != this->variableSummaries.end(); it++)
          delete it->second;
        for (auto it = this->zxSummaries.begin(); it != this->zxSummaries.end(); it++)
          delete it->second;
      }


      triton::ast::AbstractNode* AstSummaries::browseAstSummaries(triton::ast::AbstractNode* node) {
        this->allocatedNodes++;
        triton::uint32 kind = node->getKind();

        switch (kind) {

          case triton::ast::DECIMAL_NODE: {
            auto value      = static_cast<triton::ast::DecimalNode*>(node)->getValue();
            auto summaries  = static_cast<std::map<triton::uint128, triton::ast::AbstractNode*>*>((this->summaries[kind]));
            if (summaries->find(value) != summaries->end()) {
              delete node;
              return (*summaries)[value];
            }
            (*summaries)[value] = node;
            break;
          }

          case triton::ast::REFERENCE_NODE: {
            auto value      = static_cast<triton::ast::ReferenceNode*>(node)->getValue();
            auto summaries  = static_cast<std::map<triton::uint128, triton::ast::AbstractNode*>*>((this->summaries[kind]));
            if (summaries->find(value) != summaries->end()) {
              delete node;
              return (*summaries)[value];
            }
            (*summaries)[value] = node;
            break;
          }

          case triton::ast::STRING_NODE: {
            auto value      = static_cast<triton::ast::StringNode*>(node)->getValue();
            auto summaries  = static_cast<std::map<std::string, triton::ast::AbstractNode*>*>((this->summaries[kind]));
            if (summaries->find(value) != summaries->end()) {
              delete node;
              return (*summaries)[value];
            }
            (*summaries)[value] = node;
            break;
          }

          case triton::ast::VARIABLE_NODE: {
            auto value      = static_cast<triton::ast::VariableNode*>(node)->getValue();
            auto summaries  = static_cast<std::map<std::string, triton::ast::AbstractNode*>*>((this->summaries[kind]));
            if (summaries->find(value) != summaries->end()) {
              delete node;
              return (*summaries)[value];
            }
            (*summaries)[value] = node;
            break;
          }

          default: {
            auto value      = node->getChilds();
            auto summaries  = static_cast<std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*>*>((this->summaries[kind]));
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
        stats["bvdecl"]             = this->bvdeclSummaries.size();
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
        stats["declareFunction"]    = this->declareFunctionSummaries.size();
        stats["distinct"]           = this->distinctSummaries.size();
        stats["equal"]              = this->equalSummaries.size();
        stats["extract"]            = this->extractSummaries.size();
        stats["ite"]                = this->iteSummaries.size();
        stats["land"]               = this->landSummaries.size();
        stats["let"]                = this->letSummaries.size();
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

