//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/
//

#ifndef TRITON_LLVMTOTRITON_HPP
#define TRITON_LLVMTOTRITON_HPP

#include <map>
#include <memory>
#include <string>

#include <triton/ast.hpp>
#include <triton/astContext.hpp>
#include <triton/dllexport.hpp>
#include <triton/tritonTypes.hpp>

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

    //! \class LLVMToTriton
    /*! \brief Converts a LLVM IR to a Triton AST. */
    class LLVMToTriton {
      private:
        //! The Triton AST context
        triton::ast::SharedAstContext actx;

        //! Map of triton symbolic variables
        std::map<std::string, SharedAbstractNode> symvars;

        //! Converts nodes
        triton::ast::SharedAbstractNode do_convert(llvm::Value* llvmnode);

      public:
        //! Constructor.
        TRITON_EXPORT LLVMToTriton(const triton::ast::SharedAstContext& ctxt);

        //! Converts to Triton's AST
        TRITON_EXPORT triton::ast::SharedAbstractNode convert(llvm::Module* llvmModule, const char* fname="__triton");
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_LLVMTOTRITON_HPP */
