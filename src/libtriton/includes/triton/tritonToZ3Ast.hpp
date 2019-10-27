//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_TRITONTOZ3AST_H
#define TRITON_TRITONTOZ3AST_H

#include <unordered_map>
#include <z3++.h>

#include <triton/ast.hpp>
#include <triton/triton_export.h>
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
        //! This flag define if the conversion is used to evaluated a node or not.
        bool isEval;

        //! Returns the integer of the z3 expression (expr must be an int).
        triton::__uint getUintValue(const z3::expr& expr);

        //! Returns the integer of the z3 expression as a string.
        std::string getStringValue(const z3::expr& expr);

        //! The convert internal process
        z3::expr do_convert(const triton::ast::SharedAbstractNode& node, std::unordered_map<triton::ast::SharedAbstractNode, z3::expr>* output);

      protected:
        //! The z3's context.
        z3::context context;

      public:
        //! The map of symbols. E.g: (let (symbols expr1) expr2)
        std::unordered_map<std::string, triton::ast::SharedAbstractNode> symbols;

        //! The set of symbolic variables contained in the expression.
        std::unordered_map<std::string, triton::engines::symbolic::SharedSymbolicVariable> variables;

        //! Constructor.
        TRITON_EXPORT TritonToZ3Ast(bool eval=true);

        //! Converts to Z3's AST
        TRITON_EXPORT z3::expr convert(const triton::ast::SharedAbstractNode& node);
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_TRITONTOZ3AST_H */
