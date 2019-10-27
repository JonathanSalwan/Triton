//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SYMBOLICEXPRESSION_H
#define TRITON_SYMBOLICEXPRESSION_H

#include <string>
#include <memory>

#include <triton/ast.hpp>
#include <triton/triton_export.h>
#include <triton/memoryAccess.hpp>
#include <triton/register.hpp>
#include <triton/symbolicEnums.hpp>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Engines namespace
  namespace engines {
  /*!
   *  \ingroup triton
   *  \addtogroup engines
   *  @{
   */

    //! The Symbolic Execution namespace
    namespace symbolic {
    /*!
     *  \ingroup engines
     *  \addtogroup symbolic
     *  @{
     */

      //! \class SymbolicExpression
      /*! \brief The symbolic expression class */
      class SymbolicExpression {

        protected:
          //! The type of the symbolic expression assignment.
          triton::engines::symbolic::expression_e type;

          //! The root node (AST) of the symbolic expression.
          triton::ast::SharedAbstractNode ast;

          //! The comment of the symbolic expression.
          std::string comment;

          //! The symbolic expression id. This id is unique.
          triton::usize id;

          //! The origin memory address if `kind` is equal to `triton::engines::symbolic::MEM`, invalid memory otherwise.
          triton::arch::MemoryAccess originMemory;

          //! The origin register if `kind` is equal to `triton::engines::symbolic::REG`, `REG_INVALID` otherwise.
          triton::arch::Register originRegister;

        public:
          //! True if the symbolic expression is tainted.
          bool isTainted;

          //! Constructor.
          TRITON_EXPORT SymbolicExpression(const triton::ast::SharedAbstractNode& node,
                                           triton::usize id,
                                           triton::engines::symbolic::expression_e type,
                                           const std::string& comment="");

          //! Constructor by copy.
          TRITON_EXPORT SymbolicExpression(const SymbolicExpression& other);

          //! Operator.
          TRITON_EXPORT SymbolicExpression& operator=(const SymbolicExpression& other);

          //! Returns the symbolic expression id.
          TRITON_EXPORT triton::usize getId(void) const;

          //! Returns true if the symbolic expression is assigned to a memory.
          TRITON_EXPORT bool isMemory(void) const;

          //! Returns true if the symbolic expression is assigned to a register.
          TRITON_EXPORT bool isRegister(void) const;

          //! Returns true if the expression contains a symbolic variable.
          TRITON_EXPORT bool isSymbolized(void) const;

          //! Returns the type of the symbolic expression assignment.
          TRITON_EXPORT triton::engines::symbolic::expression_e getType(void) const;

          //! Returns the SMT AST root node of the symbolic expression. This is the semantics.
          TRITON_EXPORT const triton::ast::SharedAbstractNode& getAst(void) const;

          //! Returns a new SMT AST root node of the symbolic expression. This new instance is a duplicate of the original node and may be changed without changing the original semantics.
          TRITON_EXPORT triton::ast::SharedAbstractNode getNewAst(void) const;

          //! Returns the comment of the symbolic expression.
          TRITON_EXPORT const std::string& getComment(void) const;

          //! Returns the id as string of the symbolic expression according the mode of the AST representation.
          TRITON_EXPORT std::string getFormattedId(void) const;

          //! Returns the comment as string of the symbolic expression according the mode of the AST representation.
          TRITON_EXPORT std::string getFormattedComment(void) const;

          //! Returns the symbolic expression representation as string according the mode of the AST representation.
          TRITON_EXPORT std::string getFormattedExpression(void) const;

          //! Returns the origin memory access if `kind` is equal to `triton::engines::symbolic::MEM`, invalid memory otherwise.
          TRITON_EXPORT const triton::arch::MemoryAccess& getOriginMemory(void) const;

          //! Returns the origin register if `kind` is equal to `triton::engines::symbolic::REG`, `REG_INVALID` otherwise.
          TRITON_EXPORT const triton::arch::Register& getOriginRegister(void) const;

          //! Sets a root node.
          TRITON_EXPORT void setAst(const triton::ast::SharedAbstractNode& node);

          //! Sets a comment to the symbolic expression.
          TRITON_EXPORT void setComment(const std::string& comment);

          //! Sets the kind of the symbolic expression.
          TRITON_EXPORT void setType(triton::engines::symbolic::expression_e type);

          //! Sets the origin memory acccess.
          TRITON_EXPORT void setOriginMemory(const triton::arch::MemoryAccess& mem);

          //! Sets the origin register.
          TRITON_EXPORT void setOriginRegister(const triton::arch::Register& reg);
      };

      //! Shared Symbolic Expression.
      using SharedSymbolicExpression = std::shared_ptr<triton::engines::symbolic::SymbolicExpression>;

      //! Weak Symbolic Expression.
      using WeakSymbolicExpression = std::weak_ptr<triton::engines::symbolic::SymbolicExpression>;

      //! Displays a symbolic expression.
      TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const SymbolicExpression& symExpr);

      //! Displays a symbolic expression.
      TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const SymbolicExpression* symExpr);

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICEXPRESSION_H */
