//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_ASTREPRESENTATION_H
#define TRITON_ASTREPRESENTATION_H

#include <iostream>
#include "astPythonRepresentation.hpp"
#include "astRepresentationInterface.hpp"
#include "astSmtRepresentation.hpp"
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

      //! All kind of representation mode.
      enum mode_e {
        SMT_REPRESENTATION,     /*!< SMT representation */
        PYTHON_REPRESENTATION,  /*!< Python representation */
        LAST_REPRESENTATION
      };


      //! Pseudo code of SMT AST.
      class AstRepresentation {
        protected:
          //! The representation mode.
          enum mode_e mode;

          //! AstRepresentation interface.
          triton::smt2lib::representation::AstRepresentationInterface* representation[triton::smt2lib::representation::LAST_REPRESENTATION];


        public:
          //! Constructor.
          AstRepresentation();

          //! Destructor.
          ~AstRepresentation();

          //! Returns the representation mode.
          enum mode_e getMode(void);

          //! Sets the representation mode.
          void setMode(enum mode_e mode);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, smtAstAbstractNode* node);
      };

    /*! @} End of representation namespace */
    };
  /*! @} End of smt2lib namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ASTREPRESENTATION_H */
