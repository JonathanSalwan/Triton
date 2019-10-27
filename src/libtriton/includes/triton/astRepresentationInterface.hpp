//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ASTREPRESENTATIONINTERFACE_HPP
#define TRITON_ASTREPRESENTATIONINTERFACE_HPP

#include <iostream>

#include <triton/ast.hpp>
#include <triton/triton_export.h>



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

    //! The Representations namespace
    namespace representations {
    /*!
     *  \ingroup ast
     *  \addtogroup representations
     *  @{
     */

      /*!
       *  \interface AstRepresentationInterface
       *  \brief The AST representation interface.
       */
      class AstRepresentationInterface {
        public:
          //! Constructor.
          TRITON_EXPORT virtual ~AstRepresentationInterface(){};
          //! Entry point of print.
          TRITON_EXPORT virtual std::ostream& print(std::ostream& stream, triton::ast::AbstractNode* node) = 0;
      };

    /*! @} End of representations namespace */
    };
  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ASTREPRESENTATIONINTERFACE_HPP */
