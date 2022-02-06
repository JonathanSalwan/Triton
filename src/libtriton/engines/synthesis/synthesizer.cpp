//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <chrono>
#include <stack>
#include <unordered_set>
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


      SynthesisResult Synthesizer::synthesize(const triton::ast::SharedAbstractNode& input, bool constant, bool subexpr, bool opaque) {
        SynthesisResult result;

        // Save the input node
        result.setInput(input);

        // Start to record the time of the synthesizing
        auto start = std::chrono::system_clock::now();

        // Do not alter original input
        auto node = triton::ast::newInstance(input.get(), true);

        // Do the synthesize and if nothing has been synthesized, try on children expression
        if (this->do_synthesize(node, constant, opaque, result) == false) {
          if (subexpr == true) {
            while (this->childrenSynthesis(node, constant, opaque, result));
          }
        }

        //! Substitute all sub expressions
        if (this->var2expr.size()) {
          this->substituteSubExpression(result.getOutput());
        }

        // Stop to record the time of the synthesizing
        auto end = std::chrono::system_clock::now();

        // Saving the time of the synthesizing
        result.setTime(std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count());

        return result;
      }


      bool Synthesizer::do_synthesize(const triton::ast::SharedAbstractNode& node, bool constant, bool opaque, SynthesisResult& result) {
        bool ret = false;

        // How many variables in the expression?
        auto vars = triton::ast::search(node, triton::ast::VARIABLE_NODE);

        // If there is one symbolic variable, do unary operators synthesis
        if (vars.size() == 1 && node->getLevel() > 2) {
          ret = this->unaryOperatorSynthesis(vars, node, result);

          // Do also constant synthesis
          if (ret == false && constant == true) {
            ret = this->constantSynthesis(vars, node, result);
          }
        }

        // If there is two symbolic variables, do binary operators synthesis
        else if (vars.size() == 2 && node->getLevel() > 2) {
          ret = this->binaryOperatorSynthesis(vars, node, result);
        }

        // If nothing worked, do constant opaque synthesis
        if (vars.size() && ret == false && opaque == true && node->getLevel() > 2) {
          ret = this->opaqueConstantSynthesis(vars, node, result);
        }

        return ret;
      }


      bool Synthesizer::opaqueConstantSynthesis(const std::deque<triton::ast::SharedAbstractNode>& vars, const triton::ast::SharedAbstractNode& node, SynthesisResult& result) {
        /* We need Z3 solver in order to use quantifier logic */
        #ifdef TRITON_Z3_INTERFACE

        auto actx  = node->getContext();
        auto var_c = this->symbolic->newSymbolicVariable(triton::engines::symbolic::UNDEFINED_VARIABLE, 0, node->getBitvectorSize(), "");
        auto model = this->solver.getModel(actx->forall(vars, actx->equal(node, actx->variable(var_c))));

        if (model.size()) {
          auto constant = model.at(var_c->getId()).getValue();
          auto size     = model.at(var_c->getId()).getSize();

          /* Replace the constant variable to a bitvector */
          result.setOutput(actx->bv(constant, size));
          result.setSuccess(true);
          return true;
        }

        #endif

        return false;
      }


      bool Synthesizer::constantSynthesis(const std::deque<triton::ast::SharedAbstractNode>& vars, const triton::ast::SharedAbstractNode& node, SynthesisResult& result) {
        /* We need Z3 solver in order to use quantifier logic */
        #ifdef TRITON_Z3_INTERFACE

        /* We start by getting the symbolic variable of the expression */
        auto var_x = reinterpret_cast<triton::ast::VariableNode*>(vars[0].get())->getSymbolicVariable();
        auto actx  = node->getContext();

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


      bool Synthesizer::unaryOperatorSynthesis(const std::deque<triton::ast::SharedAbstractNode>& vars, const triton::ast::SharedAbstractNode& node, SynthesisResult& result) {
        /* We start by saving orignal value of symbolic variable */
        auto var_x = reinterpret_cast<triton::ast::VariableNode*>(vars[0].get())->getSymbolicVariable();
        auto actx  = node->getContext();

        triton::uint512 save_x = actx->getVariableValue(var_x->getName());
        triton::uint32  bits   = var_x->getSize();

        /* We suppose variables are 8, 16, 32 or 64-bit long */
        if (bits != 8 && bits != 16 && bits != 32 && bits != 64)
          return false;

        /*
         * NOTE: More the oracle table will grow more it will take time to looking
         *       for a potential synthesis. Currently, the complexity is O(n) where
         *       n is the number of entry in the table. At some point we have to
         *       change this.
         */
        for (auto const& it : triton::engines::synthesis::oracles::unopTable) {
          triton::ast::ast_e op = it.first;
          std::array<UnaryEntry, 40> oracles = it.second;

          // Ignore bswap oracle for 8 bit value.
          if (bits == 8 && op == triton::ast::BSWAP_NODE) {
            continue;
          }

          bool found = true;
          for (auto const& oracle : oracles) {
            // Ignore oracle that is not on same size
            if (oracle.bits != bits) {
              continue;
            }

            // Inject value
            actx->updateVariable(var_x->getName(), oracle.x);
            if (node->evaluate() != oracle.r) {
              found = false;
              break;
            }
          }

          // If an oracle is found, we craft a synthesized node.
          if (found) {
            switch (op) {
              case triton::ast::BSWAP_NODE: result.setOutput(actx->bswap(actx->variable(var_x))); break;
              case triton::ast::BVNEG_NODE: result.setOutput(actx->bvneg(actx->variable(var_x))); break;
              case triton::ast::BVNOT_NODE: result.setOutput(actx->bvnot(actx->variable(var_x))); break;
              default:
                throw triton::exceptions::SynthesizerEngine("Synthesizer::unaryOperatorSynthesis(): Invalid type of operator.");
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

        // Whatever the result, we must restore orignal value of the symbolic variable
        actx->updateVariable(var_x->getName(), save_x);

        return result.successful();
      }


      bool Synthesizer::binaryOperatorSynthesis(const std::deque<triton::ast::SharedAbstractNode>& vars, const triton::ast::SharedAbstractNode& node, SynthesisResult& result) {
        /* We start by saving orignal value of symbolic variables */
        auto var_x = reinterpret_cast<triton::ast::VariableNode*>(vars[0].get())->getSymbolicVariable();
        auto var_y = reinterpret_cast<triton::ast::VariableNode*>(vars[1].get())->getSymbolicVariable();
        auto actx  = node->getContext();

        triton::uint512 save_x = actx->getVariableValue(var_x->getName());
        triton::uint512 save_y = actx->getVariableValue(var_y->getName());
        triton::uint32  bits   = var_x->getSize();

        /* We suppose variables are on a same size */
        if (var_x->getSize() != var_y->getSize())
          return false;

        /* We suppose variables are 8, 16, 32 or 64-bit long */
        if (bits != 8 && bits != 16 && bits != 32 && bits != 64)
          return false;

        for (auto const& it : triton::engines::synthesis::oracles::binopTable) {
          triton::ast::ast_e op = it.first;
          std::array<BinaryEntry, 40> oracles = it.second;

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
              case triton::ast::BVADD_NODE:   result.setOutput(actx->bvadd(actx->variable(var_x),  actx->variable(var_y))); break;
              case triton::ast::BVAND_NODE:   result.setOutput(actx->bvand(actx->variable(var_x),  actx->variable(var_y))); break;
              case triton::ast::BVMUL_NODE:   result.setOutput(actx->bvmul(actx->variable(var_x),  actx->variable(var_y))); break;
              case triton::ast::BVNAND_NODE:  result.setOutput(actx->bvnand(actx->variable(var_x), actx->variable(var_y))); break;
              case triton::ast::BVNOR_NODE:   result.setOutput(actx->bvnor(actx->variable(var_x),  actx->variable(var_y))); break;
              case triton::ast::BVOR_NODE:    result.setOutput(actx->bvor(actx->variable(var_x),   actx->variable(var_y))); break;
              case triton::ast::BVROL_NODE:   result.setOutput(actx->bvrol(actx->variable(var_x),  actx->variable(var_y))); break;
              case triton::ast::BVROR_NODE:   result.setOutput(actx->bvror(actx->variable(var_x),  actx->variable(var_y))); break;
              case triton::ast::BVSDIV_NODE:  result.setOutput(actx->bvsdiv(actx->variable(var_x), actx->variable(var_y))); break;
              case triton::ast::BVSMOD_NODE:  result.setOutput(actx->bvsmod(actx->variable(var_x), actx->variable(var_y))); break;
              case triton::ast::BVSREM_NODE:  result.setOutput(actx->bvsrem(actx->variable(var_x), actx->variable(var_y))); break;
              case triton::ast::BVSUB_NODE:   result.setOutput(actx->bvsub(actx->variable(var_x),  actx->variable(var_y))); break;
              case triton::ast::BVUDIV_NODE:  result.setOutput(actx->bvudiv(actx->variable(var_x), actx->variable(var_y))); break;
              case triton::ast::BVUREM_NODE:  result.setOutput(actx->bvurem(actx->variable(var_x), actx->variable(var_y))); break;
              case triton::ast::BVXNOR_NODE:  result.setOutput(actx->bvxnor(actx->variable(var_x), actx->variable(var_y))); break;
              case triton::ast::BVXOR_NODE:   result.setOutput(actx->bvxor(actx->variable(var_x),  actx->variable(var_y))); break;
              default:
                throw triton::exceptions::SynthesizerEngine("Synthesizer::binaryOperatorSynthesis(): Invalid type of operator.");
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


      bool Synthesizer::childrenSynthesis(const triton::ast::SharedAbstractNode& node, bool constant, bool opaque, SynthesisResult& result) {
        std::stack<triton::ast::AbstractNode*>                worklist;
        std::unordered_set<const triton::ast::AbstractNode*>  visited;

        bool ret = false;
        worklist.push(node.get());
        while (!worklist.empty()) {
          auto current = worklist.top();
          worklist.pop();

          // This means that node is already visited and we will not need to visited it second time
          if (visited.find(current) != visited.end()) {
            continue;
          }
          visited.insert(current);

          // Unroll reference
          if (current->getType() == triton::ast::REFERENCE_NODE) {
            worklist.push(reinterpret_cast<triton::ast::ReferenceNode*>(current)->getSymbolicExpression()->getAst().get());
          }
          else {
            triton::usize index = 0;
            // Apply synthesis on every child
            for (const auto& child : current->getChildren()) {
              SynthesisResult tmp;
              if (this->do_synthesize(child, constant, opaque, tmp)) {
                /* Symbolize the sub expression */
                triton::ast::SharedAbstractNode subvar = this->symbolizeSubExpression(child, tmp);
                /* Replace the child on the fly */
                current->setChild(index++, subvar);
                /* Set true because we synthesized at least one child */
                result.setSuccess(true);
                ret = true;
                continue;
              }
              worklist.push(child.get());
              index++;
            }
          }
        }

        /*
         * If we synthesized at least one child, we set the output as 'node'
         * because it has been modified on the fly
         */
        if (result.successful()) {
          result.setOutput(node);
        }

        return ret;
      }


      triton::ast::SharedAbstractNode Synthesizer::symbolizeSubExpression(const triton::ast::SharedAbstractNode& node, SynthesisResult& tmpResult) {
        triton::ast::SharedAstContext actx      = node->getContext();
        triton::ast::SharedAbstractNode subvar  = nullptr;

        auto it =  this->hash2var.find(tmpResult.getOutput()->getHash());
        if (it != this->hash2var.end()) {
          /* If we already symbolized the node, return its symbolic variable */
          subvar = it->second;
        }
        else {
          /* Otherwise we create a new symbolic variable for this sub expression */
          subvar = actx->variable(this->symbolic->newSymbolicVariable(triton::engines::symbolic::UNDEFINED_VARIABLE, 0, node->getBitvectorSize()));
          this->hash2var.insert({tmpResult.getOutput()->getHash(), subvar});
          this->var2expr.insert({subvar, tmpResult.getOutput()});
        }

        return subvar;
      }


      void Synthesizer::substituteSubExpression(const triton::ast::SharedAbstractNode& node) {
        std::stack<triton::ast::AbstractNode*>                worklist;
        std::unordered_set<const triton::ast::AbstractNode*>  visited;

        worklist.push(node.get());
        while (!worklist.empty()) {
          auto current = worklist.top();
          worklist.pop();

          // This means that node is already visited and we will not need to visited it second time
          if (visited.find(current) != visited.end()) {
            continue;
          }
          visited.insert(current);

          // Unroll reference
          if (current->getType() == triton::ast::REFERENCE_NODE) {
            worklist.push(reinterpret_cast<triton::ast::ReferenceNode*>(current)->getSymbolicExpression()->getAst().get());
          }
          else {
            triton::usize index = 0;
            for (const auto& child : current->getChildren()) {
              if (child->getType() == triton::ast::VARIABLE_NODE) {
                auto it =  this->var2expr.find(child);
                if (it != this->var2expr.end()) {
                  auto subexpr = this->var2expr[child];
                  current->setChild(index, subexpr);
                  worklist.push(subexpr.get());
                }
              }
              else {
                worklist.push(child.get());
              }
              index++;
            }
          }
        }
      }

    }; /* synthesis namespace */
  }; /* engines namespace */
}; /* triton namespace */
