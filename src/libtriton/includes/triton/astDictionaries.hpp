//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ASTDICTIONARIES_H
#define TRITON_ASTDICTIONARIES_H

#include <set>
#include <vector>

#include <triton/ast.hpp>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The AST namespace
  namespace ast {
  /*!
   *  \ingroup triton
   *  \addtogroup ast
   *  @{
   */

    //! \class AstDictionaries
    /*! \brief The AST dictionaries class */
    class AstDictionaries {
      private:
        //! Defines if this instance is used as a backup.
        bool backupFlag;

      protected:
        //! Total of allocated nodes.
        triton::usize allocatedNodes;

        //! Total of allocated dictionaries.
        std::set<triton::ast::AbstractNode*> allocatedDictionaries;

        //! Assert Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> assertDictionary;

        //! Bvadd Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvaddDictionary;

        //! Bvand Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvandDictionary;

        //! Bvashr Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvashrDictionary;

        //! Bvdecl Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvdeclDictionary;

        //! Bvlshr Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvlshrDictionary;

        //! Bvmul Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvmulDictionary;

        //! Bvnand Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvnandDictionary;

        //! Bvneg Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvnegDictionary;

        //! Bvnor Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvnorDictionary;

        //! Bvnot Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvnotDictionary;

        //! Bvor Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvorDictionary;

        //! Bvrol Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvrolDictionary;

        //! Bvror Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvrorDictionary;

        //! Bvsdiv Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvsdivDictionary;

        //! Bvsge Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvsgeDictionary;

        //! Bvsgt Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvsgtDictionary;

        //! Bvshl Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvshlDictionary;

        //! Bvsle Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvsleDictionary;

        //! Bvslt Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvsltDictionary;

        //! Bvsmod Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvsmodDictionary;

        //! Bvsrem Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvsremDictionary;

        //! Bvsub Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvsubDictionary;

        //! Bvudiv Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvudivDictionary;

        //! Bvuge Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvugeDictionary;

        //! Bvugt Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvugtDictionary;

        //! Bvule Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvuleDictionary;

        //! Bvult Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvultDictionary;

        //! Bvurem Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvuremDictionary;

        //! Bvxnor Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvxnorDictionary;

        //! Bvxor Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvxorDictionary;

        //! Bv Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> bvDictionary;

        //! Compound Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> compoundDictionary;

        //! Concat Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> concatDictionary;

        //! Decimal Dictionary
        std::map<triton::uint512, triton::ast::AbstractNode*> decimalDictionary;

        //! Declare Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> declareFunctionDictionary;

        //! Distinct Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> distinctDictionary;

        //! Equal Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> equalDictionary;

        //! Extract Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> extractDictionary;

        //! Ite Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> iteDictionary;

        //! Land Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> landDictionary;

        //! Let Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> letDictionary;

        //! Lnot Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> lnotDictionary;

        //! Lor Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> lorDictionary;

        //! Reference Dictionary
        std::map<triton::usize, triton::ast::AbstractNode*> referenceDictionary;

        //! String Dictionary
        std::map<std::string, triton::ast::AbstractNode*> stringDictionary;

        //! Sx Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> sxDictionary;

        //! Variable Dictionary
        std::map<std::string, triton::ast::AbstractNode*> variableDictionary;

        //! Zx Dictionary
        std::map<std::vector<triton::ast::AbstractNode*>, triton::ast::AbstractNode*> zxDictionary;

        //! Dictionaries
        std::map<triton::uint32, void*> dictionaries;

    public:
        //! Constructor.
        AstDictionaries(bool isBackup=false);

        //! Constructor.
        AstDictionaries(const AstDictionaries& copy);

        //! Destructor.
        virtual ~AstDictionaries();

        //! Copies an AstDictionaries.
        void operator=(const AstDictionaries& other);

        //! Copies an AstDictionaries.
        void copy(const AstDictionaries& other);

        //! Links all sub dictionaries to the root one.
        void linkDictionaries(void);

        //! Browses into dictionaries.
        triton::ast::AbstractNode* browseAstDictionaries(triton::ast::AbstractNode* node);

        //! Returns stats about dictionaries.
        std::map<std::string, triton::usize> getAstDictionariesStats(void) const;
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ASTDICTIONARIES_H */

