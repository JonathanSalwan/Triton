//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef LIFTINGTOLLVM_HPP
#define LIFTINGTOLLVM_HPP

#include <map>
#include <memory>
#include <ostream>
#include <unordered_map>

#include <triton/ast.hpp>
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
        private:
          //! The LLVM context
          llvm::LLVMContext llvmContext;

          //! The LLVM module
          llvm::Module llvmModule;

          //! The LLVM IR builder
          llvm::IRBuilder<> llvmIR;

          //! Map Triton variables to LLVM ones
          std::map<triton::ast::SharedAbstractNode, llvm::Value*> llvmVars;

          //! Create a LLVM function
          void createFunction(const triton::engines::symbolic::SharedSymbolicExpression& expr);

          //! Converts Triton AST to LLVM IR
          llvm::Value* do_convert(const triton::ast::SharedAbstractNode& node, std::unordered_map<triton::ast::SharedAbstractNode, llvm::Value*>* results);

        public:
          //! Constructor.
          TRITON_EXPORT LiftingToLLVM();

          //! Lifts a symbolic expression and all its references to LLVM format.
          TRITON_EXPORT std::ostream& liftToLLVM(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr);
      };

    /*! @} End of lifters namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};


#endif /* LIFTINGTOLLVM_HPP */
