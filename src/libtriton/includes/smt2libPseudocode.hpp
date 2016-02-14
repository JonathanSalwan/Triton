//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SMT2LIBPSEUDOCODE_H
#define TRITON_SMT2LIBPSEUDOCODE_H

#include <iostream>
#include "smt2lib.hpp"
#include "smt2libAbstractSyntax.hpp"
#include "smt2libSmtSyntax.hpp"
#include "smt2libPythonSyntax.hpp"



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

      //! All kind of pseudocode mode.
      enum mode_e {
        SMT_SYNTAX = 0,   /*!< SMT syntax */
        PYTHON_SYNTAX,    /*!< Python syntax */
        LAST_SYNTAX
      };


      //! Pseudo code of SMT AST.
      class Pseudocode {
        protected:
          //! The pseudocode mode.
          enum mode_e mode;

          //! Syntax interface.
          triton::smt2lib::pseudocode::AbstractSyntax* syntax[triton::smt2lib::pseudocode::LAST_SYNTAX];


        public:
          //! Constructor.
          Pseudocode();

          //! Destructor.
          ~Pseudocode();

          //! Returns the pseudocode's mode.
          enum mode_e getMode(void);

          //! Sets the pseudocode's mode.
          void setMode(enum mode_e mode);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstAbstractNode* node);
      };

    /*! @} End of pseudocode namespace */
    };
  /*! @} End of smt2lib namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SMT2LIBPSEUDOCODE_H */
