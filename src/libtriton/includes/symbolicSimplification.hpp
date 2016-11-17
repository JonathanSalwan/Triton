//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SYMBOLICSIMPLIFICATION_H
#define TRITON_SYMBOLICSIMPLIFICATION_H

#include <list>

#include "ast.hpp"
#include "callbacks.hpp"
#include "tritonTypes.hpp"



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

        protected:
          //! Flag to define if we can use z3 to simplify expressions. Default: false.
          bool z3Enabled;

        public:
          //! Constructor.
          SymbolicSimplification(triton::callbacks::Callbacks* callbacks=nullptr);

          //! Constructor.
          SymbolicSimplification(const SymbolicSimplification& copy);

          //! Destructor.
          virtual ~SymbolicSimplification();

          //! Copies a SymbolicSimplification.
          void copy(const SymbolicSimplification& other);

          //! Returns true if Triton can use the simplification passes of z3.
          bool isZ3SimplificationEnabled(void) const;

          //! Enabled, Triton will use the simplification passes of z3 before to call its recorded simplification passes.
          void enableZ3Simplification(bool flag);

          //! Processes all recorded simplifications. Returns the simplified node.
          triton::ast::AbstractNode* processSimplification(triton::ast::AbstractNode* node, bool z3=false) const;

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

