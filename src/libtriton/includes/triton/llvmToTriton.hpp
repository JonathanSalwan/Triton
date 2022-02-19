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

#include <triton/api.hpp>

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
        //! The Triton AST context.
        triton::ast::SharedAstContext actx;

        //! The Triton API.
        triton::API* api;

        //! Map of triton symbolic variables.
        std::map<std::string, SharedAbstractNode> symvars;

        //! Converts nodes.
        triton::ast::SharedAbstractNode do_convert(llvm::Value* llvmnode);

        //! Gets or creates new symbolic variable.
        triton::ast::SharedAbstractNode var(const std::string& name, triton::uint32 varSize);

      public:
        //! Constructor.
        TRITON_EXPORT LLVMToTriton(triton::API& api);

        //! Constructor.
        TRITON_EXPORT LLVMToTriton(const triton::ast::SharedAstContext& ctxt);

        //! Converts a given function from an LLVM module to a Triton AST.
        TRITON_EXPORT triton::ast::SharedAbstractNode convert(llvm::Module* llvmModule, const char* fname="__triton");

        //! Converts an LLVM instruction function to a Triton AST.
        TRITON_EXPORT triton::ast::SharedAbstractNode convert(llvm::Value* instruction);
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_LLVMTOTRITON_HPP */
