//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <algorithm>
#include <list>
#include <map>
#include <vector>

#include <triton/astEnums.hpp>
#include <triton/liftingToLLVM.hpp>
#include <triton/tritonTypes.hpp>



namespace triton {
  namespace engines {
    namespace lifters {

      LiftingToLLVM::LiftingToLLVM(const triton::ast::SharedAstContext& astCtxt, triton::engines::symbolic::SymbolicEngine* symbolic)
        : astCtxt(astCtxt), symbolic(symbolic), llvmModule("tritonModule", this->llvmContext), llvmIR(this->llvmContext) {
      }


      void LiftingToLLVM::createFunction(const triton::engines::symbolic::SharedSymbolicExpression& expr) {
        // Collect used symbolic variables.
        auto vars = triton::ast::search(expr->getAst(), triton::ast::VARIABLE_NODE);

        // Each symbolic variable is a function argument
        std::vector<llvm::Type*> argsType;
        argsType.resize(vars.size());
        for (triton::usize index = 0 ; index < vars.size() ; index++) {
          switch (vars[index]->getBitvectorSize()) {
            case 8:
              argsType[index] = llvm::Type::getInt8Ty(this->llvmContext);
              break;
            case 16:
              argsType[index] = llvm::Type::getInt16Ty(this->llvmContext);
              break;
            case 32:
              argsType[index] = llvm::Type::getInt32Ty(this->llvmContext);
              break;
            case 64:
              argsType[index] = llvm::Type::getInt64Ty(this->llvmContext);
              break;
          }
        }

        /* Declare LLVM function */
        auto  retSize  = expr->getAst()->getBitvectorSize();
        auto* retType  = llvm::IntegerType::get(this->llvmContext, retSize);
        auto* funcType = llvm::FunctionType::get(retType, argsType, false /* isVarArg */);
        auto* llvmFunc = llvm::Function::Create(funcType, llvm::Function::ExternalLinkage, "__triton", this->llvmModule);

        /* Rename parameters */
        llvm::Function::arg_iterator params = llvmFunc->arg_begin();
        for (const auto& node : vars) {
          auto var = reinterpret_cast<triton::ast::VariableNode*>(node.get())->getSymbolicVariable();
          auto* param = params++;
          if (var->getAlias().empty())
            param->setName(var->getName());
          else
            param->setName(var->getAlias());
          this->llvmVars[node] = param;
        }

        // A Triton expression is represented as one basic block
        auto* llvmBasicBlock = llvm::BasicBlock::Create(this->llvmContext, "entry", llvmFunc);
        this->llvmIR.SetInsertPoint(llvmBasicBlock);
      }


      std::ostream& LiftingToLLVM::liftToLLVM(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr) {
        std::unordered_map<triton::ast::SharedAbstractNode, llvm::Value*> results;

        /* Create the LLVM function */
        this->createFunction(expr);

        /* Lift Triton AST to LLVM IR */
        auto nodes = triton::ast::childrenExtraction(expr->getAst(), true /* unroll*/, true /* revert */);
        for (const auto& node : nodes) {
          if (node->getBitvectorSize()) {
            results.insert(std::make_pair(node, this->do_convert(node, &results)));
          }
        }

        /* Create the return instruction */
        this->llvmIR.CreateRet(results.at(expr->getAst()));

        std::string dump;
        llvm::raw_string_ostream llvmStream(dump);
        this->llvmModule.print(llvmStream, nullptr);
        stream << dump;

        return stream;
      }


      llvm::Value* LiftingToLLVM::do_convert(const triton::ast::SharedAbstractNode& node, std::unordered_map<triton::ast::SharedAbstractNode, llvm::Value*>* results) {
        if (node == nullptr)
          throw triton::exceptions::AstTranslations("LiftingToLLVM::do_convert(): node cannot be null.");

        /* Prepare llvm's children */
        std::vector<llvm::Value*> children;
        for (auto&& n : node->getChildren()) {
          /* Ignore children like INTEGER_NODE */
          if (n->getBitvectorSize() == 0) {
            children.emplace_back(nullptr);
          }
          else {
            children.emplace_back(results->at(n));
          }
        }

        switch (node->getType()) {
          case triton::ast::BVADD_NODE:
            return this->llvmIR.CreateAdd(children[0], children[1]);

          case triton::ast::BVAND_NODE:
            return this->llvmIR.CreateAnd(children[0], children[1]);

          case triton::ast::BVASHR_NODE:
            return this->llvmIR.CreateAShr(children[0], children[1]);

          case triton::ast::BVLSHR_NODE:
            return this->llvmIR.CreateLShr(children[0], children[1]);

          case triton::ast::BVMUL_NODE:
            return this->llvmIR.CreateMul(children[0], children[1]);

          case triton::ast::BVNAND_NODE:
            return this->llvmIR.CreateNot(this->llvmIR.CreateAnd(children[0], children[1]));

          case triton::ast::BVNEG_NODE:
            return this->llvmIR.CreateNeg(children[0]);

          case triton::ast::BVNOR_NODE:
            return this->llvmIR.CreateNot(this->llvmIR.CreateOr(children[0], children[1]));

          case triton::ast::BVNOT_NODE:
            return this->llvmIR.CreateNot(children[0]);

          case triton::ast::BVOR_NODE:
            return this->llvmIR.CreateOr(children[0], children[1]);

          //case triton::ast::BVROL_NODE: {
          //}

          //case triton::ast::BVROR_NODE: {
          //}

          case triton::ast::BVSDIV_NODE:
            return this->llvmIR.CreateSDiv(children[0], children[1]);

          case triton::ast::BVSGE_NODE:
            return this->llvmIR.CreateICmpSGE(children[0], children[1]);

          case triton::ast::BVSGT_NODE:
            return this->llvmIR.CreateICmpSGT(children[0], children[1]);

          case triton::ast::BVSHL_NODE:
            return this->llvmIR.CreateShl(children[0], children[1]);

          case triton::ast::BVSLE_NODE:
            return this->llvmIR.CreateICmpSLE(children[0], children[1]);

          case triton::ast::BVSLT_NODE:
            return this->llvmIR.CreateICmpSLT(children[0], children[1]);

          case triton::ast::BVSMOD_NODE: {
            auto* LHS = children[0];
            auto* RHS = children[1];
            return this->llvmIR.CreateSRem(this->llvmIR.CreateAdd(this->llvmIR.CreateSRem(LHS, RHS), RHS), RHS);
          }

          case triton::ast::BVSREM_NODE:
            return this->llvmIR.CreateSRem(children[0], children[1]);

          case triton::ast::BVSUB_NODE:
            return this->llvmIR.CreateSub(children[0], children[1]);

          case triton::ast::BVUDIV_NODE:
            return this->llvmIR.CreateUDiv(children[0], children[1]);

          case triton::ast::BVUGE_NODE:
            return this->llvmIR.CreateICmpUGE(children[0], children[1]);

          case triton::ast::BVUGT_NODE:
            return this->llvmIR.CreateICmpUGT(children[0], children[1]);

          case triton::ast::BVULE_NODE:
            return this->llvmIR.CreateICmpULE(children[0], children[1]);

          case triton::ast::BVULT_NODE:
            return this->llvmIR.CreateICmpULT(children[0], children[1]);

          case triton::ast::BVUREM_NODE:
            return this->llvmIR.CreateURem(children[0], children[1]);

          case triton::ast::BVXNOR_NODE:
            return this->llvmIR.CreateNot(this->llvmIR.CreateXor(children[0], children[1]));

          case triton::ast::BVXOR_NODE:
            return this->llvmIR.CreateXor(children[0], children[1]);

          case triton::ast::BV_NODE:
            return llvm::ConstantInt::get(this->llvmContext, llvm::APInt(node->getBitvectorSize(), node->evaluate().convert_to<uint64>(), false));

          case triton::ast::CONCAT_NODE: {
            auto dstSize   = node->getBitvectorSize();
            auto finalNode = this->llvmIR.CreateZExt(children[0], llvm::IntegerType::get(this->llvmContext, dstSize));

            for (triton::usize index = 1; index < children.size(); index++) {
              finalNode = this->llvmIR.CreateShl(finalNode, node->getChildren()[index]->getBitvectorSize());
              auto* n = this->llvmIR.CreateZExt(children[index], llvm::IntegerType::get(this->llvmContext, dstSize));
              finalNode = this->llvmIR.CreateOr(finalNode, n);
            }

            return finalNode;
          }

          case triton::ast::DISTINCT_NODE:
            return this->llvmIR.CreateICmpNE(children[0], children[1]);

          case triton::ast::EQUAL_NODE:
            return this->llvmIR.CreateICmpEQ(children[0], children[1]);

          case triton::ast::EXTRACT_NODE: {
            auto  low     = reinterpret_cast<triton::ast::IntegerNode*>(node->getChildren()[1].get())->getInteger().convert_to<uint64_t>();
            auto  dstSize = node->getChildren()[2]->getBitvectorSize();
            auto* value   = children[2];

            if (low == 0) {
              return this->llvmIR.CreateTrunc(value, llvm::IntegerType::get(this->llvmContext, node->getBitvectorSize()));
            }

            return this->llvmIR.CreateTrunc(this->llvmIR.CreateLShr(value, low), llvm::IntegerType::get(this->llvmContext, node->getBitvectorSize()));
          }

          case triton::ast::ITE_NODE:
            return this->llvmIR.CreateSelect(children[0], children[1], children[2]);

          case triton::ast::LAND_NODE: {
            auto* truenode = llvm::ConstantInt::get(this->llvmContext, llvm::APInt(1, 1));
            return this->llvmIR.CreateICmpEQ(this->llvmIR.CreateAnd(children), truenode);
          }

          case triton::ast::LNOT_NODE: {
            auto* truenode = llvm::ConstantInt::get(this->llvmContext, llvm::APInt(1, 1));
            return this->llvmIR.CreateICmpEQ(this->llvmIR.CreateNot(children[0]), truenode);
          }

          case triton::ast::LOR_NODE: {
            auto* truenode = llvm::ConstantInt::get(this->llvmContext, llvm::APInt(1, 1));
            return this->llvmIR.CreateICmpEQ(this->llvmIR.CreateOr(children), truenode);
          }

          case triton::ast::LXOR_NODE: {
            auto* child0  = children[0];
            auto* child1  = children[1];
            auto* current = this->llvmIR.CreateXor(child0, child1);

            for (triton::usize index = 2; index < children.size(); index++) {
              current = this->llvmIR.CreateXor(current, children[index]);
            }

            auto* truenode = llvm::ConstantInt::get(this->llvmContext, llvm::APInt(1, 1));
            return this->llvmIR.CreateICmpEQ(current, truenode);
          }

          case triton::ast::REFERENCE_NODE:
            return results->at(reinterpret_cast<triton::ast::ReferenceNode*>(node.get())->getSymbolicExpression()->getAst());

          case triton::ast::SX_NODE:
            return this->llvmIR.CreateSExt(children[1], llvm::IntegerType::get(this->llvmContext, node->getBitvectorSize()));

          case triton::ast::VARIABLE_NODE:
            return this->llvmVars.at(node);

          case triton::ast::ZX_NODE:
            return this->llvmIR.CreateZExt(children[1], llvm::IntegerType::get(this->llvmContext, node->getBitvectorSize()));

          default:
            throw triton::exceptions::AstTranslations("LiftingToLLVM::do_convert(): Invalid kind of node.");
        }
      }

    }; /* lifters namespace */
  }; /* engines namespace */
}; /* triton namespace */
