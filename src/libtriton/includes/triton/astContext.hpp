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
#include <triton/astRepresentation.hpp>   // for AstRepresentation, astRepre...
#include <triton/dllexport.hpp>

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
      private:
        //! The AST garbage collector interface.
        triton::ast::AstGarbageCollector astGarbageCollector;

        //! String formater for ast
        triton::ast::representations::AstRepresentation astRepresentation;

        //! Map a concrete value for a variable name.
        std::map<std::string, triton::uint512> valueMapping;

      public:
        //! Constructor
        TRITON_EXPORT AstContext(const triton::modes::Modes& modes);

        //! Constructor by copy
        TRITON_EXPORT AstContext(const AstContext& other);

        //! Operator
        TRITON_EXPORT AstContext& operator=(const AstContext& other);

        //! AST C++ API - bv node builder
        TRITON_EXPORT AbstractNode* bv(triton::uint512 value, triton::uint32 size);

        //! AST C++ API - bvadd node builder
        TRITON_EXPORT AbstractNode* bvadd(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvand node builder
        TRITON_EXPORT AbstractNode* bvand(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvashr node builder
        TRITON_EXPORT AbstractNode* bvashr(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvfalse node builder
        TRITON_EXPORT AbstractNode* bvfalse(void);

        //! AST C++ API - bvlshr node builder
        TRITON_EXPORT AbstractNode* bvlshr(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvmul node builder
        TRITON_EXPORT AbstractNode* bvmul(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvnand node builder
        TRITON_EXPORT AbstractNode* bvnand(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvneg node builder
        TRITON_EXPORT AbstractNode* bvneg(AbstractNode* expr);

        //! AST C++ API - bvnor node builder
        TRITON_EXPORT AbstractNode* bvnor(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvnot node builder
        TRITON_EXPORT AbstractNode* bvnot(AbstractNode* expr);

        //! AST C++ API - bvor node builder
        TRITON_EXPORT AbstractNode* bvor(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvrol node builder
        TRITON_EXPORT AbstractNode* bvrol(triton::uint32 rot, AbstractNode* expr);

        //! AST C++ API - bvrol node builder
        TRITON_EXPORT AbstractNode* bvrol(AbstractNode* rot, AbstractNode* expr);

        //! AST C++ API - bvror node builder
        TRITON_EXPORT AbstractNode* bvror(triton::uint32 rot, AbstractNode* expr);

        //! AST C++ API - bvror node builder
        TRITON_EXPORT AbstractNode* bvror(AbstractNode* rot, AbstractNode* expr);

        //! AST C++ API - bvsdiv node builder
        TRITON_EXPORT AbstractNode* bvsdiv(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvsge node builder
        TRITON_EXPORT AbstractNode* bvsge(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvsgt node builder
        TRITON_EXPORT AbstractNode* bvsgt(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvshl node builder
        TRITON_EXPORT AbstractNode* bvshl(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvsle node builder
        TRITON_EXPORT AbstractNode* bvsle(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvslt node builder
        TRITON_EXPORT AbstractNode* bvslt(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvsmod node builder
        TRITON_EXPORT AbstractNode* bvsmod(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvsrem node builder
        TRITON_EXPORT AbstractNode* bvsrem(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvsub node builder
        TRITON_EXPORT AbstractNode* bvsub(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvtrue node builder
        TRITON_EXPORT AbstractNode* bvtrue(void);

        //! AST C++ API - bvudiv node builder
        TRITON_EXPORT AbstractNode* bvudiv(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvuge node builder
        TRITON_EXPORT AbstractNode* bvuge(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvugt node builder
        TRITON_EXPORT AbstractNode* bvugt(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvule node builder
        TRITON_EXPORT AbstractNode* bvule(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvult node builder
        TRITON_EXPORT AbstractNode* bvult(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvurem node builder
        TRITON_EXPORT AbstractNode* bvurem(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvxnor node builder
        TRITON_EXPORT AbstractNode* bvxnor(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - bvxor node builder
        TRITON_EXPORT AbstractNode* bvxor(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - concat node builder
        TRITON_EXPORT AbstractNode* concat(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - concat node builder
        template <typename T>
        AbstractNode* concat(const T& exprs);

        //! AST C++ API - decimal node builder
        TRITON_EXPORT AbstractNode* decimal(triton::uint512 value);

        //! AST C++ API - distinct node builder
        TRITON_EXPORT AbstractNode* distinct(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - equal node builder
        TRITON_EXPORT AbstractNode* equal(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - extract node builder
        TRITON_EXPORT AbstractNode* extract(triton::uint32 high, triton::uint32 low, AbstractNode* expr);

        //! AST C++ API - ite node builder
        TRITON_EXPORT AbstractNode* ite(AbstractNode* ifExpr, AbstractNode* thenExpr, AbstractNode* elseExpr);

        //! AST C++ API - land node builder
        TRITON_EXPORT AbstractNode* land(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - land node builder
        template <typename T>
        AbstractNode* land(const T& exprs);

        //! AST C++ API - let node builder
        TRITON_EXPORT AbstractNode* let(std::string alias, AbstractNode* expr2, AbstractNode* expr3);

        //! AST C++ API - lnot node builder
        TRITON_EXPORT AbstractNode* lnot(AbstractNode* expr);

        //! AST C++ API - lor node builder
        TRITON_EXPORT AbstractNode* lor(AbstractNode* expr1, AbstractNode* expr2);

        //! AST C++ API - lor node builder
        template <typename T>
        AbstractNode* lor(const T& exprs);

        //! AST C++ API - reference node builder
        TRITON_EXPORT AbstractNode* reference(triton::engines::symbolic::SymbolicExpression& expr);

        //! AST C++ API - string node builder
        TRITON_EXPORT AbstractNode* string(std::string value);

        //! AST C++ API - sx node builder
        TRITON_EXPORT AbstractNode* sx(triton::uint32 sizeExt, AbstractNode* expr);

        //! AST C++ API - variable node builder
        TRITON_EXPORT AbstractNode* variable(triton::engines::symbolic::SymbolicVariable& symVar);

        //! AST C++ API - zx node builder
        TRITON_EXPORT AbstractNode* zx(triton::uint32 sizeExt, AbstractNode* expr);

        //! Access to the underliying garbage collector
        TRITON_EXPORT triton::ast::AstGarbageCollector& getAstGarbageCollector(void);

        //! Access to the underliying garbage collector
        TRITON_EXPORT const triton::ast::AstGarbageCollector& getAstGarbageCollector(void) const;

        //! Initialize a variable in the context
        TRITON_EXPORT void initVariable(const std::string& name, const triton::uint512& value);

        //! Update a variable value in this context
        TRITON_EXPORT void updateVariable(const std::string& name, const triton::uint512& value);

        //! Access a variable value in this context
        TRITON_EXPORT const triton::uint512& getValueForVariable(const std::string& varName) const;

        //! Set the representation mode for this astContext
        TRITON_EXPORT void setRepresentationMode(triton::uint32 mode);

        //! Get the representations mode of this astContext
        TRITON_EXPORT triton::uint32 getRepresentationMode(void) const;

        //! Print the given node with this context representation
        TRITON_EXPORT std::ostream& print(std::ostream& stream, AbstractNode* node);
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_AST_CONTEXT_H */
