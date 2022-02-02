//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_LIFTINGENGINE_HPP
#define TRITON_LIFTINGENGINE_HPP

#include <triton/astContext.hpp>
#include <triton/config.hpp>
#include <triton/dllexport.hpp>
#include <triton/liftingToPython.hpp>
#include <triton/liftingToSMT.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/symbolicExpression.hpp>

#ifdef TRITON_LLVM_INTERFACE
  #include <triton/liftingToLLVM.hpp>
#endif



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
      class LiftingEngine
        : public LiftingToSMT,
          #ifdef TRITON_LLVM_INTERFACE
          public LiftingToLLVM,
          #endif
          public LiftingToPython {

        public:
          //! Constructor.
          TRITON_EXPORT LiftingEngine(const triton::ast::SharedAstContext& astCtxt, triton::engines::symbolic::SymbolicEngine* symbolic)
            : LiftingToSMT(astCtxt, symbolic),
              #ifdef TRITON_LLVM_INTERFACE
              LiftingToLLVM(),
              #endif
              LiftingToPython(astCtxt, symbolic) {
          };
      };

    /*! @} End of lifters namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_LIFTINGENGINE_HPP */
