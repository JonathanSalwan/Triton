//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_ASTREPRESENTATIONINTERFACE_HPP
#define TRITON_ASTREPRESENTATIONINTERFACE_HPP

#include <iostream>
#include "ast.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The SMT2-Lib namespace
  namespace ast {
  /*!
   *  \ingroup triton
   *  \addtogroup ast
   *  @{
   */

    //! \module The representation namespace
    namespace representation {
    /*!
     *  \ingroup ast
     *  \addtogroup representation
     *  @{
     */


      /*!
       *  \interface AstRepresentationInterface
       *  \brief The AST representation interface.
       */
      class AstRepresentationInterface {
        public:
          //! Constructor.
          virtual ~AstRepresentationInterface(){};
          //! Entry point of print.
          virtual std::ostream& print(std::ostream& stream, triton::ast::AbstractNode* node) = 0;
      };


    /*! @} End of representation namespace */
    };
  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ASTREPRESENTATIONINTERFACE_HPP */
