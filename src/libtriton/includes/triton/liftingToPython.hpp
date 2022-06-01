//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_LIFTINGTOPYTHON_HPP
#define TRITON_LIFTINGTOPYTHON_HPP

#include <ostream>

#include <triton/astContext.hpp>
#include <triton/dllexport.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/symbolicExpression.hpp>



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

    //! The Lifters namespace
    namespace lifters {
    /*!
     *  \ingroup engines
     *  \addtogroup lifters
     *  @{
     */

      //! \class LiftingToPython
      /*! \brief The lifting to Python class. */
      class LiftingToPython {
        private:
          //! Reference to the context managing ast nodes.
          triton::ast::SharedAstContext astCtxt;

          //! Instance to the symbolic engine.
          triton::engines::symbolic::SymbolicEngine* symbolic;

          //! Define required functions like ror, rol, sx and forall
          void requiredFunctions(std::ostream& stream);

        public:
          //! Constructor.
          TRITON_EXPORT LiftingToPython(const triton::ast::SharedAstContext& astCtxt, triton::engines::symbolic::SymbolicEngine* symbolic);

          //! Lifts a symbolic expression and all its references to Python format. If `icomment` is true, then print instructions assembly in expression comments.
          TRITON_EXPORT std::ostream& liftToPython(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr, bool icomment=false);
      };

    /*! @} End of lifters namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_LIFTINGTOPYTHON_HPP */
