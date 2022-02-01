//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <memory>
#include <ostream>
#include <string>

#include <triton/liftingToLLVM.hpp>
#include <triton/tritonToLLVM.hpp>



namespace triton {
  namespace engines {
    namespace lifters {

      LiftingToLLVM::LiftingToLLVM() {
      }


      std::ostream& LiftingToLLVM::liftToLLVM(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr) {
        this->liftToLLVM(stream, expr->getAst());
        return stream;
      }


      std::ostream& LiftingToLLVM::liftToLLVM(std::ostream& stream, const triton::ast::SharedAbstractNode& node) {
        /* The LLVM context */
        llvm::LLVMContext context;

        /* The lifter Triton -> LLVM */
        triton::ast::TritonToLLVM lifter(context);

        /* Lift AST to LLVM IR */
        auto llvmModule = lifter.convert(node);

        /* Print the LLVM module into the stream */
        std::string dump;
        llvm::raw_string_ostream llvmStream(dump);
        llvmModule->print(llvmStream, nullptr);
        stream << dump;

        return stream;
      }

    }; /* lifters namespace */
  }; /* engines namespace */
}; /* triton namespace */
