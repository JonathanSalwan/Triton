//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SYMBOLICEXPRESSION_H
#define TRITON_SYMBOLICEXPRESSION_H

#include <string>

#include <triton/ast.hpp>
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
          //! The kind of the symbolic expression.
          symkind_e kind;

          //! The root node (AST) of the symbolic expression.
          triton::ast::AbstractNode* ast;

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

          //! Returns the symbolic expression id.
          triton::usize getId(void) const;

          //! Returns true if the symbolic expression is assigned to a memory. \sa triton::engines::symbolic::symkind_e
          bool isMemory(void) const;

          //! Returns true if the symbolic expression is assigned to a register. \sa triton::engines::symbolic::symkind_e
          bool isRegister(void) const;

          //! Returns true if the expression contains a symbolic variable.
          bool isSymbolized(void) const;

          //! Returns the kind of the symbolic expression.
          symkind_e getKind(void) const;

          //! Returns the SMT AST root node of the symbolic expression. This is the semantics.
          triton::ast::AbstractNode* getAst(void) const;

          //! Returns a new SMT AST root node of the symbolic expression. This new instance is a duplicate of the original node and may be changed without changing the original semantics.
          triton::ast::AbstractNode* getNewAst(void) const;

          //! Returns the comment of the symbolic expression.
          const std::string& getComment(void) const;

          //! Returns the id as string of the symbolic expression according the mode of the AST representation.
          std::string getFormattedId(void) const;

          //! Returns the comment as string of the symbolic expression according the mode of the AST representation.
          std::string getFormattedComment(void) const;

          //! Returns the origin memory access if `kind` is equal to `triton::engines::symbolic::MEM`, invalid memory otherwise.
          const triton::arch::MemoryAccess& getOriginMemory(void) const;

          //! Returns the origin register if `kind` is equal to `triton::engines::symbolic::REG`, `REG_INVALID` otherwise.
          const triton::arch::Register& getOriginRegister(void) const;

          //! Sets a root node.
          void setAst(triton::ast::AbstractNode* node);

          //! Sets a comment to the symbolic expression.
          void setComment(const std::string& comment);

          //! Sets the kind of the symbolic expression.
          void setKind(symkind_e k);

          //! Sets the origin memory acccess.
          void setOriginMemory(const triton::arch::MemoryAccess& mem);

          //! Sets the origin register.
          void setOriginRegister(const triton::arch::Register& reg);

          //! Constructor.
          SymbolicExpression(triton::ast::AbstractNode* expr, triton::usize id, symkind_e kind, const std::string& comment="");

          //! Destructor.
          virtual ~SymbolicExpression();
      };

      //! Displays a symbolic expression.
      std::ostream& operator<<(std::ostream& stream, const SymbolicExpression& symExpr);

      //! Displays a symbolic expression.
      std::ostream& operator<<(std::ostream& stream, const SymbolicExpression* symExpr);

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICEXPRESSION_H */

