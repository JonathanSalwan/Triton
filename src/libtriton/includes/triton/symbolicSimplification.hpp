//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SYMBOLICSIMPLIFICATION_H
#define TRITON_SYMBOLICSIMPLIFICATION_H

#include <triton/ast.hpp>
#include <triton/callbacks.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Engines namespace
  namespace engines {
  /*!
   *  \ingroup triton
   *  \addtogroup engines
   *  @{
   */

    //! The Symbolic Execution namespace
    namespace symbolic {
    /*!
     *  \ingroup engines
     *  \addtogroup symbolic
     *  @{
     */

      //! \class SymbolicSimplification
      /*! \brief The symbolic simplification class */
      class SymbolicSimplification {
        private:
          //! Callbacks API
          triton::callbacks::Callbacks* callbacks;

        public:
          //! Constructor.
          SymbolicSimplification(triton::callbacks::Callbacks* callbacks=nullptr);

          //! Constructor.
          SymbolicSimplification(const SymbolicSimplification& copy);

          //! Destructor.
          virtual ~SymbolicSimplification();

          //! Copies a SymbolicSimplification.
          void copy(const SymbolicSimplification& other);

          //! Processes all recorded simplifications. Returns the simplified node.
          triton::ast::AbstractNode* processSimplification(triton::ast::AbstractNode* node) const;

          //! Copies a SymbolicSimplification.
          void operator=(const SymbolicSimplification& other);
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICSIMPLIFICATION_H */

