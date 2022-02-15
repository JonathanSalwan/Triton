//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <memory>
#include <ostream>
#include <string>

#include <triton/astContext.hpp>
#include <triton/liftingToLLVM.hpp>
#include <triton/llvmToTriton.hpp>
#include <triton/tritonToLLVM.hpp>

#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>



namespace triton {
  namespace engines {
    namespace lifters {

      LiftingToLLVM::LiftingToLLVM() {
      }


      std::ostream& LiftingToLLVM::liftToLLVM(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr, const char* fname, bool optimize) {
        this->liftToLLVM(stream, expr->getAst(), fname, optimize);
        return stream;
      }


      std::ostream& LiftingToLLVM::liftToLLVM(std::ostream& stream, const triton::ast::SharedAbstractNode& node, const char* fname, bool optimize) {
        /* The LLVM context */
        llvm::LLVMContext context;

        /* The lifter Triton -> LLVM */
        triton::ast::TritonToLLVM lifter(context);

        /* Lift AST to LLVM IR */
        auto llvmModule = lifter.convert(node, fname, optimize);

        /* Print the LLVM module into the stream */
        std::string dump;
        llvm::raw_string_ostream llvmStream(dump);
        llvmModule->print(llvmStream, nullptr);
        stream << dump;

        return stream;
      }


      triton::ast::SharedAbstractNode LiftingToLLVM::simplifyAstViaLLVM(const triton::ast::SharedAbstractNode& node) const {
        llvm::LLVMContext context;

        triton::ast::TritonToLLVM ttllvm(context);
        triton::ast::LLVMToTriton llvmtt(node->getContext());

        auto llvmModule = ttllvm.convert(node, "__tmp", true);  /* from triton to llvm */
        return llvmtt.convert(llvmModule.get(), "__tmp");       /* from llvm to triton */
      }

    }; /* lifters namespace */
  }; /* engines namespace */
}; /* triton namespace */
