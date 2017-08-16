//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_AST_CONTEXT_H
#define TRITON_AST_CONTEXT_H

#include <triton/ast.hpp>
#include <triton/astGarbageCollector.hpp>

#include <vector>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  namespace engines {
    namespace symbolic {
      class SymbolicExpression;
    };
  };

  //! The AST namespace
  namespace ast {
  /*!
   *  \ingroup triton
   *  \addtogroup ast
   *  @{
   */

    //! \class AstContext
    /*! \brief AST Context - Used as AST builder. */
    class AstContext {
      public:
        //! Constructor
        AstContext(const triton::modes::Modes& modes);

        //! AST C++ API - bv node builder
        AbstractNode* bv(triton::uint512 value, triton::uint32 size);

        //! AST C++ API - bvadd node builder
        AbstractNode* bvadd(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvand node builder
        AbstractNode* bvand(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvashr node builder
        AbstractNode* bvashr(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvfalse node builder
        AbstractNode* bvfalse(void);

        //! AST C++ API - bvlshr node builder
        AbstractNode* bvlshr(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvmul node builder
        AbstractNode* bvmul(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvnand node builder
        AbstractNode* bvnand(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvneg node builder
        AbstractNode* bvneg(AbstractNode* expr);

        //! AST C++ API - bvnor node builder
        AbstractNode* bvnor(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvnot node builder
        AbstractNode* bvnot(AbstractNode* expr);

        //! AST C++ API - bvor node builder
        AbstractNode* bvor(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvrol node builder
        AbstractNode* bvrol(triton::uint32 rot, AbstractNode* expr);

        //! AST C++ API - bvrol node builder
        AbstractNode* bvrol(AbstractNode* rot, AbstractNode* expr);

        //! AST C++ API - bvror node builder
        AbstractNode* bvror(triton::uint32 rot, AbstractNode* expr);

        //! AST C++ API - bvror node builder
        AbstractNode* bvror(AbstractNode* rot, AbstractNode* expr);

        //! AST C++ API - bvsdiv node builder
        AbstractNode* bvsdiv(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvsge node builder
        AbstractNode* bvsge(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvsgt node builder
        AbstractNode* bvsgt(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvshl node builder
        AbstractNode* bvshl(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvsle node builder
        AbstractNode* bvsle(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvslt node builder
        AbstractNode* bvslt(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvsmod node builder
        AbstractNode* bvsmod(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvsrem node builder
        AbstractNode* bvsrem(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvsub node builder
        AbstractNode* bvsub(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvtrue node builder
        AbstractNode* bvtrue(void);

        //! AST C++ API - bvudiv node builder
        AbstractNode* bvudiv(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvuge node builder
        AbstractNode* bvuge(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvugt node builder
        AbstractNode* bvugt(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvule node builder
        AbstractNode* bvule(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvult node builder
        AbstractNode* bvult(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvurem node builder
        AbstractNode* bvurem(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvxnor node builder
        AbstractNode* bvxnor(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvxor node builder
        AbstractNode* bvxor(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - concat node builder
        AbstractNode* concat(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - concat node builder
        template <typename T>
        AbstractNode* concat(const T& exprs);

        //! AST C++ API - decimal node builder
        AbstractNode* decimal(triton::uint512 value);

        //! AST C++ API - distinct node builder
        AbstractNode* distinct(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - equal node builder
        AbstractNode* equal(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - extract node builder
        AbstractNode* extract(triton::uint32 high, triton::uint32 low, AbstractNode* expr);

        //! AST C++ API - ite node builder
        AbstractNode* ite(AbstractNode* ifExpr, AbstractNode* thenExpr, AbstractNode* elseExpr);

        //! AST C++ API - land node builder
        AbstractNode* land(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - land node builder
        template <typename T>
        AbstractNode* land(const T& exprs);

        //! AST C++ API - let node builder
        AbstractNode* let(std::string alias, AbstractNode* expr2, AbstractNode* expr3);

        //! AST C++ API - lnot node builder
        AbstractNode* lnot(AbstractNode* expr);

        //! AST C++ API - lor node builder
        AbstractNode* lor(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - lor node builder
        template <typename T>
        AbstractNode* lor(const T& exprs);

        //! AST C++ API - reference node builder
        AbstractNode* reference(triton::engines::symbolic::SymbolicExpression& expr);

        //! AST C++ API - string node builder
        AbstractNode* string(std::string value);

        //! AST C++ API - sx node builder
        AbstractNode* sx(triton::uint32 sizeExt, AbstractNode* expr);

        //! AST C++ API - variable node builder
        AbstractNode* variable(triton::engines::symbolic::SymbolicVariable& symVar);

        //! AST C++ API - zx node builder
        AbstractNode* zx(triton::uint32 sizeExt, AbstractNode* expr);

        //! Access to the underliying garbage collector
        triton::ast::AstGarbageCollector& getAstGarbageCollector(void);

        //! Access to the underliying garbage collector
        const triton::ast::AstGarbageCollector& getAstGarbageCollector(void) const;

        //! Initialize a variable in the context
        void initVariable(const std::string& name, const triton::uint512& value);

        //! Update a variable value in this context
        void updateVariable(const std::string& name, const triton::uint512& value);

        //! Access a variable value in this context
        const triton::uint512& getValueForVariable(const std::string& varName) const;

      private:
        //! The AST garbage collector interface.
        triton::ast::AstGarbageCollector astGarbageCollector;

        //! Map a concrete value for a variable name.
        std::map<std::string, triton::uint512> valueMapping;
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_AST_CONTEXT_H */
