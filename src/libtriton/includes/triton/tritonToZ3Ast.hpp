//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_TRITONTOZ3AST_H
#define TRITON_TRITONTOZ3AST_H

#include <z3++.h>

#include <triton/ast.hpp>
#include <triton/symbolicEngine.hpp>
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

    //! \class TritonToZ3Ast
    /*! \brief Converts a Triton's AST to Z3's AST. */
    class TritonToZ3Ast {
      private:
        //! Symbolic Engine API
        triton::engines::symbolic::SymbolicEngine* symbolicEngine;

        //! This flag define if the conversion is used to evaluated a node or not.
        bool isEval;

        //! The map of symbols. E.g: (let (symbols expr1) expr2)
        std::map<std::string, triton::ast::AbstractNode*> symbols;

        //! Returns the integer of the z3 expression (expr must be an int).
        triton::__uint getUintValue(const z3::expr& expr);

        //! Returns the integer of the z3 expression as a string.
        std::string getStringValue(const z3::expr& expr);

      protected:
        //! The z3's context.
        z3::context context;

      public:
        //! Constructor.
        TritonToZ3Ast(triton::engines::symbolic::SymbolicEngine* symbolicEngine, bool eval=true);

        //! Converts to Z3's AST
        z3::expr convert(triton::ast::AbstractNode* node);
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_TRITONTOZ3AST_H */

