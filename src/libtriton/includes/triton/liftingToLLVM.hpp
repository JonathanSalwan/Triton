//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_LIFTINGTOLLVM_HPP
#define TRITON_LIFTINGTOLLVM_HPP

#include <map>
#include <memory>
#include <ostream>

#include <triton/ast.hpp>
#include <triton/dllexport.hpp>
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

      //! \class LiftingToLLVM
      /*! \brief The lifting to LLVM class. */
      class LiftingToLLVM {
        public:
          //! Constructor.
          TRITON_EXPORT LiftingToLLVM();

          //! Lifts a symbolic expression and all its references to LLVM format. `fname` represents the name of the LLVM function.
          TRITON_EXPORT std::ostream& liftToLLVM(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr, const char* fname="__triton", bool optimize=false);

          //! Lifts a abstract node and all its references to LLVM format. `fname` represents the name of the LLVM function.
          TRITON_EXPORT std::ostream& liftToLLVM(std::ostream& stream, const triton::ast::SharedAbstractNode& node, const char* fname="__triton", bool optimize=false);

          //! Lifts and simplify an AST using LLVM
          TRITON_EXPORT triton::ast::SharedAbstractNode simplifyAstViaLLVM(const triton::ast::SharedAbstractNode& node) const;
      };

    /*! @} End of lifters namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_LIFTINGTOLLVM_HPP */
