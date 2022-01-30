//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef LIFTINGENGINE_HPP
#define LIFTINGENGINE_HPP

#include <triton/astContext.hpp>
#include <triton/liftingToSMT.hpp>
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

      //! \class LiftingEngine
      /*! \brief The lifting engine class. */
      class LiftingEngine : public LiftingToSMT {
        public:
          //! Constructor.
          TRITON_EXPORT LiftingEngine(const triton::ast::SharedAstContext& astCtxt, triton::engines::symbolic::SymbolicEngine* symbolic)
            : LiftingToSMT(astCtxt, symbolic) {
          };
      };

    /*! @} End of lifters namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* LIFTINGENGINE_HPP */
