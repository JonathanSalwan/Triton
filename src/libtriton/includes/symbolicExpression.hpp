//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SYMBOLICEXPRESSION_H
#define TRITON_SYMBOLICEXPRESSION_H

#include <string>
#include "registerOperand.hpp"
#include "ast.hpp"
#include "tritonTypes.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Engines namespace
  namespace engines {
  /*!
   *  \ingroup triton
   *  \addtogroup engines
   *  @{
   */

    //! \module The Symbolic Execution namespace
    namespace symbolic {
    /*!
     *  \ingroup engines
     *  \addtogroup symbolic
     *  @{
     */

      //! Defines the kind of symbolic variables.
      enum symkind_e {
        UNDEF = 0, //!< Undefined
        REG,       //!< Assigned to a register.
        MEM        //!< Assigned to a memory.
      };


      //! \class SymbolicExpression
      /*! \brief The symbolic expression class */
      class SymbolicExpression {

        protected:
          //! The kind of the symbolic expression.
          symkind_e kind;

          //! The root node (AST SMT2-Lib) of the symbolic expression.
          triton::ast::AbstractNode* ast;

          //! The comment of the symbolic expression.
          std::string comment;

          //! The symbolic expression id. This id is unique.
          triton::__uint id;

          //! The origin memory address if `kind` is equal to `triton::engines::symbolic::MEM`, 0 otherwise.
          triton::__uint originAddress;

          //! The origin register if `kind` is equal to `triton::engines::symbolic::REG`, `REG_INVALID` otherwise.
          triton::arch::RegisterOperand originRegister;

        public:
          //! True if the symbolic expression is tainted.
          bool isTainted;

          //! Returns the symbolic expression id.
          triton::__uint getId(void);

          //! Returns true if the symbolic expression is assigned to a memory. \sa triton::engines::symbolic::symkind_e
          bool isMemory(void);

          //! Returns true if the symbolic expression is assigned to a register. \sa triton::engines::symbolic::symkind_e
          bool isRegister(void);

          //! Returns the kind of the symbolic expression.
          symkind_e getKind(void);

          //! Returns the SMT AST root node of the symbolic expression. This is the semantics.
          triton::ast::AbstractNode* getAst(void);

          //! Returns a new SMT AST root node of the symbolic expression. This new instance is a duplicate of the original node and may be changed without changing the original semantics.
          triton::ast::AbstractNode* getNewAst(void);

          //! Returns the comment of the symbolic expression.
          std::string getComment(void);

          //! Returns the id as string of the symbolic expression.
          std::string getId2Str(void);

          //! Returns the origin memory address if `kind` is equal to `triton::engines::symbolic::MEM`, 0 otherwise.
          triton::__uint getOriginAddress(void);

          //! Returns the origin register if `kind` is equal to `triton::engines::symbolic::REG`, `REG_INVALID` otherwise.
          triton::arch::RegisterOperand& getOriginRegister(void);

          //! Sets a root node.
          void setAst(triton::ast::AbstractNode* node);

          //! Sets the kind of the symbolic expression.
          void setKind(symkind_e k);

          //! Sets the origin memory address.
          void setOriginAddress(triton::__uint addr);

          //! Sets the origin register.
          void setOriginRegister(triton::arch::RegisterOperand& reg);

          //! Constructor.
          SymbolicExpression(triton::ast::AbstractNode* expr, triton::__uint id, symkind_e kind, std::string comment="");

          //! Destructor.
          ~SymbolicExpression();
      };

      //! Displays a symbolic expression.
      std::ostream& operator<<(std::ostream& stream, SymbolicExpression symExpr);

      //! Displays a symbolic expression.
      std::ostream& operator<<(std::ostream& stream, SymbolicExpression* symExpr);

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICEXPRESSION_H */

