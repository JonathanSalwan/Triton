//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_AST_CONTEXT_H
#define TRITON_AST_CONTEXT_H

#include <map>
#include <memory>
#include <vector>
#include <list>

#include <triton/ast.hpp>
#include <triton/astRepresentation.hpp>
#include <triton/triton_export.h>
#include <triton/exceptions.hpp>
#include <triton/modes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  /* Forward declarations */
  namespace engines {
    namespace symbolic {
      class SymbolicExpression;
      using SharedSymbolicExpression = std::shared_ptr<triton::engines::symbolic::SymbolicExpression>;

      class SymbolicVariable;
      using SharedSymbolicVariable = std::shared_ptr<triton::engines::symbolic::SymbolicVariable>;
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
    class AstContext : public std::enable_shared_from_this<AstContext> {
      private:
        //! Modes API
        triton::modes::SharedModes modes;

        //! String formater for ast
        triton::ast::representations::AstRepresentation astRepresentation;

        //! Maps a concrete value and ast node for a variable name.
        std::map<std::string, std::pair<triton::ast::WeakAbstractNode, triton::uint512>> valueMapping;

      public:
        //! Constructor
        TRITON_EXPORT AstContext(const triton::modes::SharedModes& modes);

        //! Destructor
        TRITON_EXPORT ~AstContext();

        //! Operator
        TRITON_EXPORT AstContext& operator=(const AstContext& other);

        //! AST C++ API - assert node builder
        TRITON_EXPORT SharedAbstractNode assert_(const SharedAbstractNode& expr);

        //! AST C++ API - bv node builder
        TRITON_EXPORT SharedAbstractNode bv(const triton::uint512& value, triton::uint32 size);

        //! AST C++ API - bvadd node builder
        TRITON_EXPORT SharedAbstractNode bvadd(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvand node builder
        TRITON_EXPORT SharedAbstractNode bvand(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvashr node builder
        TRITON_EXPORT SharedAbstractNode bvashr(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvfalse node builder
        TRITON_EXPORT SharedAbstractNode bvfalse(void);

        //! AST C++ API - bvlshr node builder
        TRITON_EXPORT SharedAbstractNode bvlshr(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvmul node builder
        TRITON_EXPORT SharedAbstractNode bvmul(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvnand node builder
        TRITON_EXPORT SharedAbstractNode bvnand(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvneg node builder
        TRITON_EXPORT SharedAbstractNode bvneg(const SharedAbstractNode& expr);

        //! AST C++ API - bvnor node builder
        TRITON_EXPORT SharedAbstractNode bvnor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvnot node builder
        TRITON_EXPORT SharedAbstractNode bvnot(const SharedAbstractNode& expr);

        //! AST C++ API - bvor node builder
        TRITON_EXPORT SharedAbstractNode bvor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvrol node builder
        TRITON_EXPORT SharedAbstractNode bvrol(const SharedAbstractNode& expr, triton::uint32 rot);

        //! AST C++ API - bvrol node builder
        TRITON_EXPORT SharedAbstractNode bvrol(const SharedAbstractNode& expr, const SharedAbstractNode& rot);

        //! AST C++ API - bvror node builder
        TRITON_EXPORT SharedAbstractNode bvror(const SharedAbstractNode& expr, triton::uint32 rot);

        //! AST C++ API - bvror node builder
        TRITON_EXPORT SharedAbstractNode bvror(const SharedAbstractNode& expr, const SharedAbstractNode& rot);

        //! AST C++ API - bvsdiv node builder
        TRITON_EXPORT SharedAbstractNode bvsdiv(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvsge node builder
        TRITON_EXPORT SharedAbstractNode bvsge(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvsgt node builder
        TRITON_EXPORT SharedAbstractNode bvsgt(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvshl node builder
        TRITON_EXPORT SharedAbstractNode bvshl(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvsle node builder
        TRITON_EXPORT SharedAbstractNode bvsle(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvslt node builder
        TRITON_EXPORT SharedAbstractNode bvslt(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvsmod node builder
        TRITON_EXPORT SharedAbstractNode bvsmod(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvsrem node builder
        TRITON_EXPORT SharedAbstractNode bvsrem(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvsub node builder
        TRITON_EXPORT SharedAbstractNode bvsub(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvtrue node builder
        TRITON_EXPORT SharedAbstractNode bvtrue(void);

        //! AST C++ API - bvudiv node builder
        TRITON_EXPORT SharedAbstractNode bvudiv(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvuge node builder
        TRITON_EXPORT SharedAbstractNode bvuge(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvugt node builder
        TRITON_EXPORT SharedAbstractNode bvugt(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvule node builder
        TRITON_EXPORT SharedAbstractNode bvule(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvult node builder
        TRITON_EXPORT SharedAbstractNode bvult(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvurem node builder
        TRITON_EXPORT SharedAbstractNode bvurem(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvxnor node builder
        TRITON_EXPORT SharedAbstractNode bvxnor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - bvxor node builder
        TRITON_EXPORT SharedAbstractNode bvxor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - compound node builder
        template <typename T> SharedAbstractNode compound(const T& exprs) {
          SharedAbstractNode node = std::make_shared<CompoundNode>(exprs, this->shared_from_this());
          if (node == nullptr)
            throw triton::exceptions::Ast("Node builders - Not enough memory");
          node->init();
          return node;
        }

        //! AST C++ API - concat node builder
        TRITON_EXPORT SharedAbstractNode concat(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - concat node builder
        template <typename T> SharedAbstractNode concat(const T& exprs) {
          SharedAbstractNode node = std::make_shared<ConcatNode>(exprs, this->shared_from_this());
          if (node == nullptr)
            throw triton::exceptions::Ast("Node builders - Not enough memory");
          node->init();
          return node;
        }

        //! AST C++ API - declare node builder
        TRITON_EXPORT SharedAbstractNode declare(const SharedAbstractNode& var);

        //! AST C++ API - distinct node builder
        TRITON_EXPORT SharedAbstractNode distinct(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - equal node builder
        TRITON_EXPORT SharedAbstractNode equal(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - extract node builder
        TRITON_EXPORT SharedAbstractNode extract(triton::uint32 high, triton::uint32 low, const SharedAbstractNode& expr);

        //! AST C++ API - iff node builder
        TRITON_EXPORT SharedAbstractNode iff(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - integer node builder
        TRITON_EXPORT SharedAbstractNode integer(const triton::uint512& value);

        //! AST C++ API - ite node builder
        TRITON_EXPORT SharedAbstractNode ite(const SharedAbstractNode& ifExpr, const SharedAbstractNode& thenExpr, const SharedAbstractNode& elseExpr);

        //! AST C++ API - land node builder
        TRITON_EXPORT SharedAbstractNode land(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - land node builder
        template <typename T> SharedAbstractNode land(const T& exprs) {
          SharedAbstractNode node = std::make_shared<LandNode>(exprs, this->shared_from_this());
          if (node == nullptr)
            throw triton::exceptions::Ast("Node builders - Not enough memory");
          node->init();
          return node;
        }

        //! AST C++ API - let node builder
        TRITON_EXPORT SharedAbstractNode let(std::string alias, const SharedAbstractNode& expr2, const SharedAbstractNode& expr3);

        //! AST C++ API - lnot node builder
        TRITON_EXPORT SharedAbstractNode lnot(const SharedAbstractNode& expr);

        //! AST C++ API - lor node builder
        TRITON_EXPORT SharedAbstractNode lor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - lor node builder
        template <typename T> SharedAbstractNode lor(const T& exprs) {
          SharedAbstractNode node = std::make_shared<LorNode>(exprs, this->shared_from_this());
          if (node == nullptr)
            throw triton::exceptions::Ast("Node builders - Not enough memory");
          node->init();
          return node;
        }

        //! AST C++ API - lxor node builder
        TRITON_EXPORT SharedAbstractNode lxor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);

        //! AST C++ API - lxor node builder
        template <typename T> SharedAbstractNode lxor(const T& exprs) {
          SharedAbstractNode node = std::make_shared<LxorNode>(exprs, this->shared_from_this());
          if (node == nullptr)
            throw triton::exceptions::Ast("Node builders - Not enough memory");
          node->init();
          return node;
        }

        //! AST C++ API - reference node builder
        TRITON_EXPORT SharedAbstractNode reference(const triton::engines::symbolic::SharedSymbolicExpression& expr);

        //! AST C++ API - string node builder
        TRITON_EXPORT SharedAbstractNode string(std::string value);

        //! AST C++ API - sx node builder
        TRITON_EXPORT SharedAbstractNode sx(triton::uint32 sizeExt, const SharedAbstractNode& expr);

        //! AST C++ API - variable node builder
        TRITON_EXPORT SharedAbstractNode variable(const triton::engines::symbolic::SharedSymbolicVariable& symVar);

        //! AST C++ API - zx node builder
        TRITON_EXPORT SharedAbstractNode zx(triton::uint32 sizeExt, const SharedAbstractNode& expr);

        //! Initializes a variable in the context
        TRITON_EXPORT void initVariable(const std::string& name, const triton::uint512& value, const SharedAbstractNode& node);

        //! Updates a variable value in this context
        TRITON_EXPORT void updateVariable(const std::string& name, const triton::uint512& value);

        //! Gets a variable node from its name.
        SharedAbstractNode getVariableNode(const std::string& name);

        //! Gets a variable value from its name.
        TRITON_EXPORT const triton::uint512& getVariableValue(const std::string& name) const;

        //! Sets the representation mode for this astContext
        TRITON_EXPORT void setRepresentationMode(triton::uint32 mode);

        //! Gets the representations mode of this astContext
        TRITON_EXPORT triton::uint32 getRepresentationMode(void) const;

        //! Prints the given node with this context representation
        TRITON_EXPORT std::ostream& print(std::ostream& stream, AbstractNode* node);
    };

    //! Shared AST context
    using SharedAstContext = std::shared_ptr<triton::ast::AstContext>;

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_AST_CONTEXT_H */
