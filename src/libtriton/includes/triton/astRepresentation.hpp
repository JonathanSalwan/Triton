//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_ASTREPRESENTATION_H
#define TRITON_ASTREPRESENTATION_H

#include <iostream>
#include <memory>

#include <triton/ast.hpp>
#include <triton/astEnums.hpp>
#include <triton/astPythonRepresentation.hpp>
#include <triton/astRepresentationInterface.hpp>
#include <triton/astSmtRepresentation.hpp>
#include <triton/dllexport.hpp>



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

      //! Pseudo code of SMT AST.
      class AstRepresentation {
        protected:
          //! The representation mode.
          triton::ast::representations::mode_e mode;

          //! AstRepresentation interface.
          std::unique_ptr<triton::ast::representations::AstRepresentationInterface> representations[triton::ast::representations::LAST_REPRESENTATION];

        public:
          //! Constructor.
          TRITON_EXPORT AstRepresentation();

          //! Constructor.
          TRITON_EXPORT AstRepresentation(const AstRepresentation& other);

          //! Operator.
          TRITON_EXPORT AstRepresentation& operator=(const AstRepresentation& other);

          //! Returns the representation mode.
          TRITON_EXPORT triton::ast::representations::mode_e getMode(void) const;

          //! Sets the representation mode.
          TRITON_EXPORT void setMode(triton::ast::representations::mode_e mode);

          //! Prints the node according to the current representation mode.
          TRITON_EXPORT std::ostream& print(std::ostream& stream, AbstractNode* node);
      };

    /*! @} End of representations namespace */
    };
  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ASTREPRESENTATION_H */
