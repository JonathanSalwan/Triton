//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_Z3INTERFACE_HPP
#define TRITON_Z3INTERFACE_HPP

#include <tritoncore/types.hpp>

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

    //! \ingroup ast
    //! \addtogroup Z3Interface
    /*! \brief The interface between Triton and Z3 */
    namespace Z3Interface {
        //! Converts a Triton's AST to a Z3's AST, perform a Z3 simplification and returns a Triton's AST.
        triton::ast::SharedAbstractNode simplify(triton::ast::AbstractNode* node);

        //! Evaluates a Triton's AST via Z3 and returns a concrete value.
        triton::uint512 evaluate(triton::ast::AbstractNode *node);

    /*! @} End of Z3Interface namespace */
    };
  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_Z3INTERFACE_HPP */
