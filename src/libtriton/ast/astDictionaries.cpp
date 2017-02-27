//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/astDictionaries.hpp>



namespace triton {
  namespace ast {

    AstDictionaries::AstDictionaries(bool isBackup) {
      this->allocatedNodes  = 0;
      this->backupFlag      = isBackup;

      this->linkDictionaries();
    }


    AstDictionaries::AstDictionaries(const AstDictionaries& copy) {
      this->copy(copy);
    }


    AstDictionaries::~AstDictionaries() {
      if (this->backupFlag == false) {
        for (auto it = this->allocatedDictionaries.begin(); it != this->allocatedDictionaries.end(); it++)
          delete *it;
      }
    }


    void AstDictionaries::operator=(const AstDictionaries& other) {
      this->copy(other);
    }


    void AstDictionaries::copy(const AstDictionaries& other) {
      /* Global information */
      this->allocatedNodes              = other.allocatedNodes;
      this->allocatedDictionaries       = other.allocatedDictionaries;
      this->backupFlag                  = true;

      /* Dictionnaries */
      this->assertDictionary            = other.assertDictionary;
      this->bvaddDictionary             = other.bvaddDictionary;
      this->bvandDictionary             = other.bvandDictionary;
      this->bvashrDictionary            = other.bvashrDictionary;
      this->bvdeclDictionary            = other.bvdeclDictionary;
      this->bvlshrDictionary            = other.bvlshrDictionary;
      this->bvmulDictionary             = other.bvmulDictionary;
      this->bvnandDictionary            = other.bvnandDictionary;
      this->bvnegDictionary             = other.bvnegDictionary;
      this->bvnorDictionary             = other.bvnorDictionary;
      this->bvnotDictionary             = other.bvnotDictionary;
      this->bvorDictionary              = other.bvorDictionary;
      this->bvrolDictionary             = other.bvrolDictionary;
      this->bvrorDictionary             = other.bvrorDictionary;
      this->bvsdivDictionary            = other.bvsdivDictionary;
      this->bvsgeDictionary             = other.bvsgeDictionary;
      this->bvsgtDictionary             = other.bvsgtDictionary;
      this->bvshlDictionary             = other.bvshlDictionary;
      this->bvsleDictionary             = other.bvsleDictionary;
      this->bvsltDictionary             = other.bvsltDictionary;
      this->bvsmodDictionary            = other.bvsmodDictionary;
      this->bvsremDictionary            = other.bvsremDictionary;
      this->bvsubDictionary             = other.bvsubDictionary;
      this->bvudivDictionary            = other.bvudivDictionary;
      this->bvugeDictionary             = other.bvugeDictionary;
      this->bvugtDictionary             = other.bvugtDictionary;
      this->bvuleDictionary             = other.bvuleDictionary;
      this->bvultDictionary             = other.bvultDictionary;
      this->bvuremDictionary            = other.bvuremDictionary;
      this->bvxnorDictionary            = other.bvxnorDictionary;
      this->bvxorDictionary             = other.bvxorDictionary;
      this->bvDictionary                = other.bvDictionary;
      this->compoundDictionary          = other.compoundDictionary;
      this->concatDictionary            = other.concatDictionary;
      this->decimalDictionary           = other.decimalDictionary;
      this->declareFunctionDictionary   = other.declareFunctionDictionary;
      this->distinctDictionary          = other.distinctDictionary;
      this->equalDictionary             = other.equalDictionary;
      this->extractDictionary           = other.extractDictionary;
      this->iteDictionary               = other.iteDictionary;
      this->landDictionary              = other.landDictionary;
      this->letDictionary               = other.letDictionary;
      this->lnotDictionary              = other.lnotDictionary;
      this->lorDictionary               = other.lorDictionary;
      this->referenceDictionary         = other.referenceDictionary;
      this->stringDictionary            = other.stringDictionary;
      this->sxDictionary                = other.sxDictionary;
      this->variableDictionary          = other.variableDictionary;
      this->zxDictionary                = other.zxDictionary;

      this->linkDictionaries();
    }


    void AstDictionaries::linkDictionaries(void) {
      this->dictionaries[triton::ast::ASSERT_NODE]             = &this->assertDictionary;
      this->dictionaries[triton::ast::BVADD_NODE]              = &this->bvaddDictionary;
      this->dictionaries[triton::ast::BVAND_NODE]              = &this->bvandDictionary;
      this->dictionaries[triton::ast::BVASHR_NODE]             = &this->bvashrDictionary;
      this->dictionaries[triton::ast::BVDECL_NODE]             = &this->bvdeclDictionary;
      this->dictionaries[triton::ast::BVLSHR_NODE]             = &this->bvlshrDictionary;
      this->dictionaries[triton::ast::BVMUL_NODE]              = &this->bvmulDictionary;
      this->dictionaries[triton::ast::BVNAND_NODE]             = &this->bvnandDictionary;
      this->dictionaries[triton::ast::BVNEG_NODE]              = &this->bvnegDictionary;
      this->dictionaries[triton::ast::BVNOR_NODE]              = &this->bvnorDictionary;
      this->dictionaries[triton::ast::BVNOT_NODE]              = &this->bvnotDictionary;
      this->dictionaries[triton::ast::BVOR_NODE]               = &this->bvorDictionary;
      this->dictionaries[triton::ast::BVROL_NODE]              = &this->bvrolDictionary;
      this->dictionaries[triton::ast::BVROR_NODE]              = &this->bvrorDictionary;
      this->dictionaries[triton::ast::BVSDIV_NODE]             = &this->bvsdivDictionary;
      this->dictionaries[triton::ast::BVSGE_NODE]              = &this->bvsgeDictionary;
      this->dictionaries[triton::ast::BVSGT_NODE]              = &this->bvsgtDictionary;
      this->dictionaries[triton::ast::BVSHL_NODE]              = &this->bvshlDictionary;
      this->dictionaries[triton::ast::BVSLE_NODE]              = &this->bvsleDictionary;
      this->dictionaries[triton::ast::BVSLT_NODE]              = &this->bvsltDictionary;
      this->dictionaries[triton::ast::BVSMOD_NODE]             = &this->bvsmodDictionary;
      this->dictionaries[triton::ast::BVSREM_NODE]             = &this->bvsremDictionary;
      this->dictionaries[triton::ast::BVSUB_NODE]              = &this->bvsubDictionary;
      this->dictionaries[triton::ast::BVUDIV_NODE]             = &this->bvudivDictionary;
      this->dictionaries[triton::ast::BVUGE_NODE]              = &this->bvugeDictionary;
      this->dictionaries[triton::ast::BVUGT_NODE]              = &this->bvugtDictionary;
      this->dictionaries[triton::ast::BVULE_NODE]              = &this->bvuleDictionary;
      this->dictionaries[triton::ast::BVULT_NODE]              = &this->bvultDictionary;
      this->dictionaries[triton::ast::BVUREM_NODE]             = &this->bvuremDictionary;
      this->dictionaries[triton::ast::BVXNOR_NODE]             = &this->bvxnorDictionary;
      this->dictionaries[triton::ast::BVXOR_NODE]              = &this->bvxorDictionary;
      this->dictionaries[triton::ast::BV_NODE]                 = &this->bvDictionary;
      this->dictionaries[triton::ast::COMPOUND_NODE]           = &this->compoundDictionary;
      this->dictionaries[triton::ast::CONCAT_NODE]             = &this->concatDictionary;
      this->dictionaries[triton::ast::DECIMAL_NODE]            = &this->decimalDictionary;
      this->dictionaries[triton::ast::DECLARE_FUNCTION_NODE]   = &this->declareFunctionDictionary;
      this->dictionaries[triton::ast::DISTINCT_NODE]           = &this->distinctDictionary;
      this->dictionaries[triton::ast::EQUAL_NODE]              = &this->equalDictionary;
      this->dictionaries[triton::ast::EXTRACT_NODE]            = &this->extractDictionary;
      this->dictionaries[triton::ast::ITE_NODE]                = &this->iteDictionary;
      this->dictionaries[triton::ast::LAND_NODE]               = &this->landDictionary;
      this->dictionaries[triton::ast::LET_NODE]                = &this->letDictionary;
      this->dictionaries[triton::ast::LNOT_NODE]               = &this->lnotDictionary;
      this->dictionaries[triton::ast::LOR_NODE]                = &this->lorDictionary;
      this->dictionaries[triton::ast::REFERENCE_NODE]          = &this->referenceDictionary;
      this->dictionaries[triton::ast::STRING_NODE]             = &this->stringDictionary;
      this->dictionaries[triton::ast::SX_NODE]                 = &this->sxDictionary;
      this->dictionaries[triton::ast::VARIABLE_NODE]           = &this->variableDictionary;
      this->dictionaries[triton::ast::ZX_NODE]                 = &this->zxDictionary;
    }


    triton::ast::AbstractNode* AstDictionaries::browseAstDictionaries(triton::ast::AbstractNode* node) {
      this->allocatedNodes++;
      triton::uint32 kind = node->getKind();

      switch (kind) {

        case triton::ast::DECIMAL_NODE: {
          auto value       = static_cast<triton::ast::DecimalNode*>(node)->getValue();
          auto dictionary  = static_cast<std::map<triton::uint512, triton::ast::AbstractNode*>*>((this->dictionaries[kind]));
          if (dictionary->find(value) != dictionary->end()) {
            delete node;
            return (*dictionary)[value];
          }
          (*dictionary)[value] = node;
          break;
        }

        case triton::ast::REFERENCE_NODE: {
          auto value       = static_cast<triton::ast::ReferenceNode*>(node)->getValue();
          auto dictionary  = static_cast<std::map<triton::usize, triton::ast::AbstractNode*>*>((this->dictionaries[kind]));
          if (dictionary->find(value) != dictionary->end()) {
            delete node;
            return (*dictionary)[value];
          }
          (*dictionary)[value] = node;
          break;
        }

        case triton::ast::STRING_NODE: {
          auto value       = static_cast<triton::ast::StringNode*>(node)->getValue();
          auto dictionary  = static_cast<std::map<std::string, triton::ast::AbstractNode*>*>((this->dictionaries[kind]));
          if (dictionary->find(value) != dictionary->end()) {
            delete node;
            return (*dictionary)[value];
          }
          (*dictionary)[value] = node;
          break;
        }

        case triton::ast::VARIABLE_NODE: {
          auto value       = static_cast<triton::ast::VariableNode*>(node)->getValue();
          auto dictionary  = static_cast<std::map<std::string, triton::ast::AbstractNode*>*>((this->dictionaries[kind]));
          if (dictionary->find(value) != dictionary->end()) {
            delete node;
            return (*dictionary)[value];
          }
          (*dictionary)[value] = node;
          break;
        }

        default: {
          auto value       = node->getChilds();
          auto dictionary  = static_cast<std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*>*>((this->dictionaries[kind]));
          if (dictionary->find(value) != dictionary->end()) {
            delete node;
            return (*dictionary)[value];
          }
          (*dictionary)[value] = node;
          break;
        }

      }

      this->allocatedDictionaries.insert(node);
      return nullptr;
    }


    std::map<std::string, triton::usize> AstDictionaries::getAstDictionariesStats(void) const {
      std::map<std::string, triton::usize> stats;
      stats["assert"]                 = this->assertDictionary.size();
      stats["bvadd"]                  = this->bvaddDictionary.size();
      stats["bvand"]                  = this->bvandDictionary.size();
      stats["bvashr"]                 = this->bvashrDictionary.size();
      stats["bvdecl"]                 = this->bvdeclDictionary.size();
      stats["bvlshr"]                 = this->bvlshrDictionary.size();
      stats["bvmul"]                  = this->bvmulDictionary.size();
      stats["bvnand"]                 = this->bvnandDictionary.size();
      stats["bvneg"]                  = this->bvnegDictionary.size();
      stats["bvnor"]                  = this->bvnorDictionary.size();
      stats["bvnot"]                  = this->bvnotDictionary.size();
      stats["bvor"]                   = this->bvorDictionary.size();
      stats["bvrol"]                  = this->bvrolDictionary.size();
      stats["bvror"]                  = this->bvrorDictionary.size();
      stats["bvsdiv"]                 = this->bvsdivDictionary.size();
      stats["bvsge"]                  = this->bvsgeDictionary.size();
      stats["bvsgt"]                  = this->bvsgtDictionary.size();
      stats["bvshl"]                  = this->bvshlDictionary.size();
      stats["bvsle"]                  = this->bvsleDictionary.size();
      stats["bvslt"]                  = this->bvsltDictionary.size();
      stats["bvsmod"]                 = this->bvsmodDictionary.size();
      stats["bvsrem"]                 = this->bvsremDictionary.size();
      stats["bvsub"]                  = this->bvsubDictionary.size();
      stats["bvudiv"]                 = this->bvudivDictionary.size();
      stats["bvuge"]                  = this->bvugeDictionary.size();
      stats["bvugt"]                  = this->bvugtDictionary.size();
      stats["bvule"]                  = this->bvuleDictionary.size();
      stats["bvult"]                  = this->bvultDictionary.size();
      stats["bvurem"]                 = this->bvuremDictionary.size();
      stats["bvxnor"]                 = this->bvxnorDictionary.size();
      stats["bvxor"]                  = this->bvxorDictionary.size();
      stats["bv"]                     = this->bvDictionary.size();
      stats["compound"]               = this->compoundDictionary.size();
      stats["concat"]                 = this->concatDictionary.size();
      stats["decimal"]                = this->decimalDictionary.size();
      stats["declareFunction"]        = this->declareFunctionDictionary.size();
      stats["distinct"]               = this->distinctDictionary.size();
      stats["equal"]                  = this->equalDictionary.size();
      stats["extract"]                = this->extractDictionary.size();
      stats["ite"]                    = this->iteDictionary.size();
      stats["land"]                   = this->landDictionary.size();
      stats["let"]                    = this->letDictionary.size();
      stats["lnot"]                   = this->lnotDictionary.size();
      stats["lor"]                    = this->lorDictionary.size();
      stats["reference"]              = this->referenceDictionary.size();
      stats["string"]                 = this->stringDictionary.size();
      stats["sx"]                     = this->sxDictionary.size();
      stats["variable"]               = this->variableDictionary.size();
      stats["zx"]                     = this->zxDictionary.size();
      stats["allocatedDictionaries"]  = this->allocatedDictionaries.size();
      stats["allocatedNodes"]         = this->allocatedNodes;
      return stats;
    }

  }; /* ast namespace */
}; /*triton namespace */

