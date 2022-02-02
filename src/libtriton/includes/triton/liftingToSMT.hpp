//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_LIFTINGTOSMT_HPP
#define TRITON_LIFTINGTOSMT_HPP

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

      //! \class LiftingToSMT
      /*! \brief The lifting to SMT class. */
      class LiftingToSMT {
        private:
          //! Reference to the context managing ast nodes.
          triton::ast::SharedAstContext astCtxt;

          //! Instance to the symbolic engine.
          triton::engines::symbolic::SymbolicEngine* symbolic;

        public:
          //! Constructor.
          TRITON_EXPORT LiftingToSMT(const triton::ast::SharedAstContext& astCtxt, triton::engines::symbolic::SymbolicEngine* symbolic);

          //! Lifts a symbolic expression and all its references to SMT format. If `assert_` is true, then (assert <expr>).
          TRITON_EXPORT std::ostream& liftToSMT(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr, bool assert_);
      };

    /*! @} End of lifters namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* LIFTINGTOSMT_HPP */
