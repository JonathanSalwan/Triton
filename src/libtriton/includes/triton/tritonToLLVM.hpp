//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_TRITONTOLLVM_HPP
#define TRITON_TRITONTOLLVM_HPP

#include <map>
#include <memory>
#include <unordered_map>

#include <triton/ast.hpp>
#include <triton/dllexport.hpp>

#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>



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

    //! \class TritonToLLVM
    /*! \brief Converts a Triton's AST to LVM IR. */
    class TritonToLLVM {
      private:
        //! The LLVM context.
        llvm::LLVMContext& llvmContext;

        //! The LLVM module.
        std::shared_ptr<llvm::Module> llvmModule;

        //! The LLVM IR builder.
        llvm::IRBuilder<> llvmIR;

        //! Map Triton variables to LLVM ones.
        std::map<triton::ast::SharedAbstractNode, llvm::Value*> llvmVars;

        //! Create a LLVM function. `fname` represents the name of the LLVM function.
        void createFunction(const triton::ast::SharedAbstractNode& node, const char* fname);

        //! Converts Triton AST to LLVM IR.
        llvm::Value* do_convert(const triton::ast::SharedAbstractNode& node, std::unordered_map<triton::ast::SharedAbstractNode, llvm::Value*>* results);

      public:
        //! Constructor.
        TRITON_EXPORT TritonToLLVM(llvm::LLVMContext& llvmContext);

        //! Lifts a symbolic expression and all its references to LLVM format. `fname` represents the name of the LLVM function.
        TRITON_EXPORT std::shared_ptr<llvm::Module> convert(const triton::ast::SharedAbstractNode& node, const char* fname="__triton", bool optimize=false);
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_TRITONTOLLVM_HPP */
