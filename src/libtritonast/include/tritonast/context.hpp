//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_AST_CONTEXT_H
#define TRITON_AST_CONTEXT_H

#include <tritonast/nodes.hpp>
#include "tritonast/representations/representation.hpp"   // for Representation, Repre...

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

    //! \class Context
    /*! \brief AST Context - Used as AST builder. */
    class Context {
      public:
        Context() = default;

        Context(Context const&) = delete;
        Context(Context &&) = default;

        Context& operator=(Context const&) = delete;
        Context& operator=(Context &&) = default;

        ~Context() = default;

      public:
        //! AST C++ API - bv node builder
        SharedAbstractNode bv(triton::uint512 value, triton::uint32 size);

        //! AST C++ API - bvadd node builder
        SharedAbstractNode bvadd(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvand node builder
        SharedAbstractNode bvand(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvashr node builder
        SharedAbstractNode bvashr(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvfalse node builder
        SharedAbstractNode bvfalse(void);

        //! AST C++ API - bvlshr node builder
        SharedAbstractNode bvlshr(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvmul node builder
        SharedAbstractNode bvmul(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvnand node builder
        SharedAbstractNode bvnand(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvneg node builder
        SharedAbstractNode bvneg(SharedAbstractNode expr);

        //! AST C++ API - bvnor node builder
        SharedAbstractNode bvnor(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvnot node builder
        SharedAbstractNode bvnot(SharedAbstractNode expr);

        //! AST C++ API - bvor node builder
        SharedAbstractNode bvor(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvrol node builder
        SharedAbstractNode bvrol(triton::uint32 rot, SharedAbstractNode expr);

        //! AST C++ API - bvrol node builder
        SharedAbstractNode bvrol(SharedAbstractNode rot, SharedAbstractNode expr);

        //! AST C++ API - bvror node builder
        SharedAbstractNode bvror(triton::uint32 rot, SharedAbstractNode expr);

        //! AST C++ API - bvror node builder
        SharedAbstractNode bvror(SharedAbstractNode rot, SharedAbstractNode expr);

        //! AST C++ API - bvsdiv node builder
        SharedAbstractNode bvsdiv(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvsge node builder
        SharedAbstractNode bvsge(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvsgt node builder
        SharedAbstractNode bvsgt(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvshl node builder
        SharedAbstractNode bvshl(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvsle node builder
        SharedAbstractNode bvsle(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvslt node builder
        SharedAbstractNode bvslt(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvsmod node builder
        SharedAbstractNode bvsmod(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvsrem node builder
        SharedAbstractNode bvsrem(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvsub node builder
        SharedAbstractNode bvsub(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvtrue node builder
        SharedAbstractNode bvtrue(void);

        //! AST C++ API - bvudiv node builder
        SharedAbstractNode bvudiv(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvuge node builder
        SharedAbstractNode bvuge(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvugt node builder
        SharedAbstractNode bvugt(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvule node builder
        SharedAbstractNode bvule(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvult node builder
        SharedAbstractNode bvult(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvurem node builder
        SharedAbstractNode bvurem(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvxnor node builder
        SharedAbstractNode bvxnor(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - bvxor node builder
        SharedAbstractNode bvxor(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - concat node builder
        SharedAbstractNode concat(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - concat node builder
        template <typename T>
        SharedAbstractNode concat(const T& exprs);

        //! AST C++ API - decimal node builder
        SharedAbstractNode decimal(triton::uint512 value);

        //! AST C++ API - distinct node builder
        SharedAbstractNode distinct(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - equal node builder
        SharedAbstractNode equal(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - extract node builder
        SharedAbstractNode extract(triton::uint32 high, triton::uint32 low, SharedAbstractNode expr);

        //! AST C++ API - ite node builder
        SharedAbstractNode ite(SharedAbstractNode ifExpr, SharedAbstractNode thenExpr, SharedAbstractNode elseExpr);

        //! AST C++ API - land node builder
        SharedAbstractNode land(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - land node builder
        template <typename T>
        SharedAbstractNode land(const T& exprs);

        //! AST C++ API - let node builder
        SharedAbstractNode let(std::string alias, SharedAbstractNode expr2, SharedAbstractNode expr3);

        //! AST C++ API - lnot node builder
        SharedAbstractNode lnot(SharedAbstractNode expr);

        //! AST C++ API - lor node builder
        SharedAbstractNode lor(SharedAbstractNode expr1, SharedAbstractNode expr2);

        //! AST C++ API - lor node builder
        template <typename T>
        SharedAbstractNode lor(const T& exprs);

        //! AST C++ API - reference node builder
        SharedAbstractNode reference(SharedAbstractNode ast, size_t id, std::function<void()> const& end);

        //! AST C++ API - string node builder
        SharedAbstractNode string(std::string value);

        //! AST C++ API - sx node builder
        SharedAbstractNode sx(triton::uint32 sizeExt, SharedAbstractNode expr);

        //! AST C++ API - variable node builder
        SharedAbstractNode variable(std::string const& varName, triton::uint32 size);

        //! AST C++ API - zx node builder
        SharedAbstractNode zx(triton::uint32 sizeExt, SharedAbstractNode expr);

        //! Initialize a variable in the context
        void initVariable(const std::string& name, const triton::uint512& value, SharedAbstractNode const& node);

        //! Get existing variable node if present or nullptr
        SharedAbstractNode getVariableNode(const std::string& name);

        //! Update a variable value in this context
        void updateVariable(const std::string& name, const triton::uint512& value);

        //! Access a variable value in this context
        const triton::uint512& getValueForVariable(const std::string& varName) const;

        //! Set the representation mode for this astContext
        void setRepresentationMode(triton::uint32 mode);

        //! Get the representations mode of this astContext
        triton::uint32 getRepresentationMode(void) const;

        //! Print the given node with this context representation
        std::ostream& print(std::ostream& stream, AbstractNode* node);

      private:
        //! Map a concrete value and ast node for a variable name.
        // FIXME: Could be a weakptr to avoid leaking these nodes
        std::map<std::string, std::pair<triton::ast::SharedAbstractNode, triton::uint512>> valueMapping;

        //! String formater for ast
        triton::ast::representations::Representation astRepresentation;
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_AST_CONTEXT_H */
