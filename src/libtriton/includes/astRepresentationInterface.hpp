//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_ASTREPRESENTATIONINTERFACE_HPP
#define TRITON_ASTREPRESENTATIONINTERFACE_HPP

#include <iostream>
#include "smt2lib.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The SMT2-Lib namespace
  namespace smt2lib {
  /*!
   *  \ingroup triton
   *  \addtogroup smt2-lib
   *  @{
   */

    //! \module The representation namespace
    namespace representation {
    /*!
     *  \ingroup smt2-lib
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
          virtual std::ostream& print(std::ostream& stream, triton::smt2lib::smtAstAbstractNode* node) = 0;
      };


    /*! @} End of representation namespace */
    };
  /*! @} End of smt2lib namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ASTREPRESENTATIONINTERFACE_HPP */
