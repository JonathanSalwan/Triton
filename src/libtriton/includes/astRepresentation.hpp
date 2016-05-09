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
#include "ast.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The AST namespace
  namespace ast {
  /*!
   *  \ingroup triton
   *  \addtogroup ast
   *  @{
   */

    //! \module The Representations namespace
    namespace representations {
    /*!
     *  \ingroup ast
     *  \addtogroup representations
     *  @{
     */

      //! All kinds of representation mode.
      enum mode_e {
        SMT_REPRESENTATION,     /*!< SMT representation */
        PYTHON_REPRESENTATION,  /*!< Python representation */
        LAST_REPRESENTATION
      };


      //! Pseudo code of SMT AST.
      class AstRepresentation {
        protected:
          //! The representation mode.
          triton::uint32 mode;

          //! AstRepresentation interface.
          triton::ast::representations::AstRepresentationInterface* representations[triton::ast::representations::LAST_REPRESENTATION];


        public:
          //! Constructor.
          AstRepresentation();

          //! Destructor.
          ~AstRepresentation();

          //! Returns the representation mode.
          triton::uint32 getMode(void) const;

          //! Sets the representation mode.
          void setMode(triton::uint32 mode);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, AbstractNode* node);
      };

    /*! @} End of representations namespace */
    };
  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ASTREPRESENTATION_H */
