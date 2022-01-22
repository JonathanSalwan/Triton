//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <chrono>
#include <vector>

#include <triton/ast.hpp>
#include <triton/exceptions.hpp>
#include <triton/oracleEntry.hpp>
#include <triton/symbolicVariable.hpp>
#include <triton/synthesizer.hpp>



namespace triton {
  namespace engines {
    namespace synthesis {

      Synthesizer::Synthesizer(triton::engines::symbolic::SymbolicEngine* symbolic)
        : symbolic(symbolic) {
        #ifdef TRITON_Z3_INTERFACE
        this->solver.setSolver(triton::engines::solver::SOLVER_Z3);
        #endif
      }


      SynthesisResult Synthesizer::synthesize(const triton::ast::SharedAbstractNode& input, bool constant) {
        SynthesisResult result;

        // Save the input node
        result.setInput(input);

        // Start to record the time of the synthesizing
        auto start = std::chrono::system_clock::now();

        auto actx = input->getContext();
        auto vars = triton::ast::search(input, triton::ast::VARIABLE_NODE);

        if (constant && vars.size() == 1 && input->getLevel() > 2) {
          this->constantSynthesis(actx, vars, input, result);
        }

        else if (vars.size() == 2 && input->getLevel() > 2) {
          this->twoVariablesSynthesis(actx, vars, input, result);
        }

        // Stop to record the time of the synthesizing
        auto end = std::chrono::system_clock::now();

        // Saving the time of the synthesizing
        result.setTime(std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count());

        return result;
      }


      bool Synthesizer::constantSynthesis(const triton::ast::SharedAstContext& actx, const std::deque<triton::ast::SharedAbstractNode>& vars,
                                          const triton::ast::SharedAbstractNode& node, SynthesisResult& result) {
        /* We need Z3 solver in order to use quantifier logic */
        #ifdef TRITON_Z3_INTERFACE

        /* We start by getting the symbolic variable of the expression */
        auto var_x = reinterpret_cast<triton::ast::VariableNode*>(vars[0].get())->getSymbolicVariable();

        triton::uint32 bits    = var_x->getSize();
        triton::uint32 insize  = node->getBitvectorSize();
        triton::uint32 outsize = bits;

        /* We suppose variables are 8, 16, 32 or 64-bit long */
        if ((bits != 8 && bits != 16 && bits != 32 && bits != 64) || insize != outsize)
          return false;

        /* We create the constant variable */
        auto var_c = this->symbolic->newSymbolicVariable(triton::engines::symbolic::UNDEFINED_VARIABLE, 0, bits, "");

        /* Create the constant operator table */
        std::array<ConstantEntry, 6> operatorTable = {
          ConstantEntry(1, actx->bvadd(actx->variable(var_x), actx->variable(var_c))), // x + c
          ConstantEntry(1, actx->bvand(actx->variable(var_x), actx->variable(var_c))), // x & c
          ConstantEntry(1, actx->bvmul(actx->variable(var_x), actx->variable(var_c))), // x * c
          ConstantEntry(0, actx->bvsub(actx->variable(var_c), actx->variable(var_x))), // c - x
          ConstantEntry(1, actx->bvsub(actx->variable(var_x), actx->variable(var_c))), // x - c
          ConstantEntry(1, actx->bvxor(actx->variable(var_x), actx->variable(var_c)))  // x ^ c
        };

        std::vector<triton::ast::SharedAbstractNode> x = {actx->variable(var_x)};
        for (auto const& entry : operatorTable) {
          /* For all X, there exists a constant C, such that operator is equal to node */
          auto model = this->solver.getModel(actx->forall(x, actx->equal(entry.op, node)));
          /* If a constant is found */
          if (model.size()) {
            auto constant = model.at(var_c->getId()).getValue();
            auto size     = model.at(var_c->getId()).getSize();
            auto output   = triton::ast::newInstance(entry.op.get());

            /* Replace the constant variable to a bitvector */
            output->setChild(entry.position, actx->bv(constant, size));
            result.setOutput(output);
            result.setSuccess(true);
            return true;
          }
        }

        #endif
        return false;
      }


      bool Synthesizer::twoVariablesSynthesis(const triton::ast::SharedAstContext& actx, const std::deque<triton::ast::SharedAbstractNode>& vars,
                                              const triton::ast::SharedAbstractNode& node, SynthesisResult& result) {
        /* We start by saving orignal value of symbolic variables */
        auto var_x = reinterpret_cast<triton::ast::VariableNode*>(vars[0].get())->getSymbolicVariable();
        auto var_y = reinterpret_cast<triton::ast::VariableNode*>(vars[1].get())->getSymbolicVariable();

        triton::uint512 save_x = actx->getVariableValue(var_x->getName());
        triton::uint512 save_y = actx->getVariableValue(var_y->getName());
        triton::uint32  bits   = var_x->getSize();

        /* We suppose variables are 8, 16, 32 or 64-bit long */
        if (bits != 8 && bits != 16 && bits != 32 && bits != 64)
          return false;

        for (auto const& it : triton::engines::synthesis::oracleTable) {
          triton::ast::ast_e op = it.first;
          std::array<OracleEntry, 40> oracles = it.second;

          bool found = true;
          for (auto const& oracle : oracles) {
            // Ignore oracle that is not on same size
            if (oracle.bits != bits) {
              continue;
            }

            // Inject values
            actx->updateVariable(var_x->getName(), oracle.x);
            actx->updateVariable(var_y->getName(), oracle.y);
            if (node->evaluate() != oracle.r) {
              found = false;
              break;
            }
          }

          // If an oracle is found, we craft a synthesized node.
          if (found) {
            switch (op) {
              case triton::ast::BVADD_NODE: result.setOutput(actx->bvadd(actx->variable(var_x), actx->variable(var_y)));  break;
              case triton::ast::BVAND_NODE: result.setOutput(actx->bvand(actx->variable(var_x), actx->variable(var_y)));  break;
              case triton::ast::BVMUL_NODE: result.setOutput(actx->bvmul(actx->variable(var_x), actx->variable(var_y)));  break;
              case triton::ast::BVOR_NODE:  result.setOutput(actx->bvor(actx->variable(var_x),  actx->variable(var_y)));  break;
              case triton::ast::BVSUB_NODE: result.setOutput(actx->bvsub(actx->variable(var_x), actx->variable(var_y)));  break;
              case triton::ast::BVXOR_NODE: result.setOutput(actx->bvxor(actx->variable(var_x), actx->variable(var_y)));  break;
              default:
                throw triton::exceptions::SynthesizerEngine("Synthesizer::twoVariablesSynthesis(): Invalid type of operator.");
            }

            // Adjust the size of the destination
            auto out     = result.getOutput();
            auto in      = node;
            auto outsize = out->getBitvectorSize();
            auto insize  = in->getBitvectorSize();
            if (insize > outsize) {
              result.setOutput(actx->zx(insize - outsize, out));
            }

            // Stop iterating over oracles
            result.setSuccess(true);
            break;
          }
          // If not found, continuing to iterate over oracles
        }

        // Whatever the result, we must restore orignal value of symbolic variables
        actx->updateVariable(var_x->getName(), save_x);
        actx->updateVariable(var_y->getName(), save_y);

        return result.successful();
      }

    }; /* synthesis namespace */
  }; /* engines namespace */
}; /* triton namespace */
