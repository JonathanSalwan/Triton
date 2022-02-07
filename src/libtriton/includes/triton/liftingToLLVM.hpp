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

#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>



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

          //! Lifts a symbolic expression and all its references to LLVM format.
          TRITON_EXPORT std::ostream& liftToLLVM(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr);

          //! Lifts a abstract node and all its references to LLVM format.
          TRITON_EXPORT std::ostream& liftToLLVM(std::ostream& stream, const triton::ast::SharedAbstractNode& node);
      };

    /*! @} End of lifters namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_LIFTINGTOLLVM_HPP */
