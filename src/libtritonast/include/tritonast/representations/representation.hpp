//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ASTREPRESENTATION_H
#define TRITON_ASTREPRESENTATION_H

#include <tritonast/representations/python.hpp>
#include <tritonast/representations/representationInterface.hpp>
#include <tritonast/representations/smt.hpp>

#include <iostream>
#include <memory>


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

      //! All kinds of representation mode.
      enum mode_e {
        SMT_REPRESENTATION,     /*!< SMT representation */
        PYTHON_REPRESENTATION,  /*!< Python representation */
        LAST_REPRESENTATION
      };

      //! Pseudo code of SMT AST.
      class Representation {
        protected:
          //! The representation mode.
          triton::uint32 mode;

          //! Representation interface.
          std::unique_ptr<triton::ast::representations::RepresentationInterface> representations[triton::ast::representations::LAST_REPRESENTATION];

        public:
          //! Constructor.
          Representation();

          Representation(Representation &&) = default;
          Representation(Representation const&) = delete;

          ~Representation() = default;

          Representation& operator=(Representation const&) = delete;
          Representation& operator=(Representation &&) = default;

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
