//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_TRITONTOZ3AST_H
#define TRITON_TRITONTOZ3AST_H

#include <tritonast/nodes.hpp>

#include <z3++.h>

#include <stack>



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

      #if defined(__i386) || defined(_M_IX86)
      using __uint = decltype(std::declval<z3::expr>().get_numeral_uint());
      #endif
      #if defined(__x86_64__) || defined(_M_X64)
      using __uint = decltype(std::declval<z3::expr>().get_numeral_uint64());
      #endif

      private:
        //! This flag define if the conversion is used to evaluated a node or not.
        bool isEval;

        //! Returns the integer of the z3 expression (expr must be an int).
        __uint getUintValue(const z3::expr& expr);

        //! Returns the integer of the z3 expression as a string.
        std::string getStringValue(const z3::expr& expr);

      protected:
        //! The z3's context.
        // WARNING: This context should live longer than symbols and refs so we
        // *must* declare it *before*
        z3::context context;

        //! The map of symbols. E.g: (let (symbols expr1) expr2)
        std::map<std::string, z3::expr> symbols;
        std::map<triton::uint32, z3::expr> refs;

      public:
        //! Constructor.
        TritonToZ3Ast(bool eval=true);

        //! Converts to Z3's AST
        z3::expr convert(triton::ast::AbstractNode* node);

        z3::expr do_convert(triton::ast::AbstractNode* node, std::stack<z3::expr> & childs);
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_TRITONTOZ3AST_H */

