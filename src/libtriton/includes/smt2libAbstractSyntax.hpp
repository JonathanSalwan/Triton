//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SMT2LIBABSTRACTSYNTAX_HPP
#define TRITON_SMT2LIBABSTRACTSYNTAX_HPP

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

    //! \module The pseudocode namespace
    namespace pseudocode {
    /*!
     *  \ingroup smt2lib
     *  \addtogroup pseudocode
     *  @{
     */


      //! Syntax interface.
      class AbstractSyntax {
        public:
          //! Constructor.
          virtual ~AbstractSyntax(){};
          //! Entry point of display.
          virtual std::ostream& display(std::ostream& stream, triton::smt2lib::smtAstAbstractNode* node) = 0;
      };


    /*! @} End of pseudocode namespace */
    };
  /*! @} End of smt2lib namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SMT2LIBABSTRACTSYNTAX_HPP */
