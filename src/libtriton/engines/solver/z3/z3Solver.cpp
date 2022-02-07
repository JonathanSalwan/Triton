//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <chrono>
#include <string>

#include <triton/astContext.hpp>
#include <triton/exceptions.hpp>
#include <triton/solverModel.hpp>
#include <triton/symbolicVariable.hpp>
#include <triton/tritonToZ3.hpp>
#include <triton/tritonTypes.hpp>
#include <triton/z3Solver.hpp>
#include <triton/z3ToTriton.hpp>



namespace triton {
  namespace engines {
    namespace solver {

      z3::expr Z3Solver::mk_or(z3::expr_vector args) {
        std::vector<Z3_ast> array;

        for (triton::uint32 i = 0; i < args.size(); i++)
          array.push_back(args[i]);

        return to_expr(args.ctx(), Z3_mk_or(args.ctx(), static_cast<triton::uint32>(array.size()), &(array[0])));
      }


      Z3Solver::Z3Solver() {
        this->timeout = 0;
        this->memoryLimit = 0;
      }


      std::vector<std::unordered_map<triton::usize, SolverModel>> Z3Solver::getModels(const triton::ast::SharedAbstractNode& node, triton::uint32 limit, triton::engines::solver::status_e* status, triton::uint32 timeout, triton::uint32* solvingTime) const {
        std::vector<std::unordered_map<triton::usize, SolverModel>> ret;
        triton::ast::SharedAbstractNode onode = node;
        triton::ast::TritonToZ3 z3Ast{false};

        try {
          if (onode == nullptr)
            throw triton::exceptions::SolverEngine("Z3Solver::getModels(): node cannot be null.");

          /* Z3 does not need an assert() as root node */
          if (node->getType() == triton::ast::ASSERT_NODE)
            onode = node->getChildren()[0];

          if (onode->isLogical() == false)
            throw triton::exceptions::SolverEngine("Z3Solver::getModels(): Must be a logical node.");

          z3::expr      expr = z3Ast.convert(onode);
          z3::context&  ctx  = expr.ctx();
          z3::solver    solver(ctx);

          /* Create a solver and add the expression */
          solver.add(expr);

          z3::params p(ctx);

          /* Define the timeout */
          if (timeout) {
            p.set(":timeout", timeout);
          }
          else if (this->timeout) {
            p.set(":timeout", this->timeout);
          }

          /* Define memory limit */
          if (this->memoryLimit) {
            p.set(":max_memory", this->memoryLimit);
          }

          solver.set(p);

          /* Get time of solving start */
          auto start = std::chrono::system_clock::now();

          /* Get first model */
          z3::check_result res = solver.check();

          /* Write back the status code of the first constraint */
          this->writeBackStatus(solver, res, status);

          /* Check if it is sat */
          while (res == z3::sat && limit >= 1) {
            /* Get model */
            z3::model m = solver.get_model();

            /* Traversing the model */
            std::unordered_map<triton::usize, SolverModel> smodel;
            z3::expr_vector args(ctx);
            for (triton::uint32 i = 0; i < m.size(); i++) {

              /* Get the z3 variable */
              z3::func_decl z3Variable = m[i];

              /* Get the name as std::string from a z3 variable */
              std::string varName = z3Variable.name().str();

              /* Get z3 expr */
              z3::expr exp = m.get_const_interp(z3Variable);

              /* Get the size of a z3 expr */
              triton::uint32 bvSize = exp.get_sort().bv_size();

              /* Get the value of a z3 expr */
              std::string svalue = Z3_get_numeral_string(ctx, exp);

              /* Convert a string value to a integer value */
              triton::uint512 value = triton::uint512(svalue);

              /* Create a triton model */
              SolverModel trionModel = SolverModel(z3Ast.variables[varName], value);

              /* Map the result */
              smodel[trionModel.getId()] = trionModel;

              /* Uniq result */
              if (exp.get_sort().is_bv())
                args.push_back(ctx.bv_const(varName.c_str(), bvSize) != ctx.bv_val(svalue.c_str(), bvSize));
            }

            /* Check that model is available */
            if (smodel.empty())
              break;

            /* Push model */
            ret.push_back(smodel);

            if (--limit) {
              /* Escape last models */
              if (!args.empty()) {
                solver.add(this->mk_or(args));
              }

              /* Get next model */
              res = solver.check();
            }
          }

          /* Get time of solving end */
          auto end = std::chrono::system_clock::now();

          if (solvingTime)
            *solvingTime = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
        }
        catch (const z3::exception& e) {
          if (!strcmp(e.msg(), "max. memory exceeded")) {
            if (status) {
              *status = triton::engines::solver::OUTOFMEM;
            }
            return {};
          }
          throw triton::exceptions::SolverEngine(std::string("Z3Solver::getModels(): ") + e.msg());
        }

        return ret;
      }


      bool Z3Solver::isSat(const triton::ast::SharedAbstractNode& node, triton::engines::solver::status_e* status, triton::uint32 timeout, triton::uint32* solvingTime) const {
        triton::ast::TritonToZ3 z3Ast{false};

        if (node == nullptr)
          throw triton::exceptions::SolverEngine("Z3Solver::isSat(): node cannot be null.");

        if (node->isLogical() == false)
          throw triton::exceptions::SolverEngine("Z3Solver::isSat(): Must be a logical node.");

        try {
          z3::expr      expr = z3Ast.convert(node);
          z3::context&  ctx  = expr.ctx();
          z3::solver    solver(ctx);

          /* Create a solver and add the expression */
          solver.add(expr);

          z3::params p(ctx);

          /* Define the timeout */
          if (timeout) {
            p.set(":timeout", timeout);
          }
          else if (this->timeout) {
            p.set(":timeout", this->timeout);
          }

          /* Define memory limit */
          if (this->memoryLimit) {
            p.set(":max_memory", this->memoryLimit);
          }

          solver.set(p);

          /* Get time of solving start */
          auto start = std::chrono::system_clock::now();

          z3::check_result res = solver.check();

          /* Get time of solving end */
          auto end = std::chrono::system_clock::now();

          if (solvingTime)
            *solvingTime = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();

          this->writeBackStatus(solver, res, status);
          return res == z3::sat;
        }
        catch (const z3::exception& e) {
          if (!strcmp(e.msg(), "max. memory exceeded")) {
            if (status) {
              *status = triton::engines::solver::OUTOFMEM;
            }
            return {};
          }
          throw triton::exceptions::SolverEngine(std::string("Z3Solver::isSat(): ") + e.msg());
        }
      }


      std::unordered_map<triton::usize, SolverModel> Z3Solver::getModel(const triton::ast::SharedAbstractNode& node, triton::engines::solver::status_e* status, triton::uint32 timeout, triton::uint32 *solvingTime) const {
        std::unordered_map<triton::usize, SolverModel> ret;
        std::vector<std::unordered_map<triton::usize, SolverModel>> allModels;

        allModels = this->getModels(node, 1, status, timeout, solvingTime);
        if (allModels.size() > 0)
          ret = allModels.front();

        return ret;
      }


      triton::ast::SharedAbstractNode Z3Solver::simplify(const triton::ast::SharedAbstractNode& node) const {
        if (node == nullptr)
          throw triton::exceptions::AstLifting("Z3Solver::simplify(): node cannot be null.");

        try {
          triton::ast::TritonToZ3 z3Ast{false};
          triton::ast::Z3ToTriton tritonAst{node->getContext()};

          /* From Triton to Z3 */
          z3::expr expr = z3Ast.convert(node);

          /* Simplify and back to Triton's AST */
          auto snode = tritonAst.convert(expr.simplify());

          return snode;
        }
        catch (const z3::exception& e) {
          throw triton::exceptions::AstLifting(std::string("Z3Solver::evaluate(): ") + e.msg());
        }
      }


      triton::uint512 Z3Solver::evaluate(const triton::ast::SharedAbstractNode& node) const {
        if (node == nullptr)
          throw triton::exceptions::AstLifting("Z3Solver::simplify(): node cannot be null.");

        try {
          triton::ast::TritonToZ3 z3ast{true};

          /* From Triton to Z3 */
          z3::expr expr = z3ast.convert(node);

          /* Simplify the expression to get a constant */
          expr = expr.simplify();

          triton::uint512 res = 0;
          if (expr.get_sort().is_bool())
            res = Z3_get_bool_value(expr.ctx(), expr) == Z3_L_TRUE ? true : false;
          else
            res = triton::uint512{Z3_get_numeral_string(expr.ctx(), expr)};

          return res;
        }
        catch (const z3::exception& e) {
          throw triton::exceptions::AstLifting(std::string("Z3Solver::evaluate(): ") + e.msg());
        }
      }


      void Z3Solver::writeBackStatus(z3::solver& solver, z3::check_result res, triton::engines::solver::status_e* status) const {
        if (status != nullptr) {
          switch (res) {
            case z3::sat:
              *status = triton::engines::solver::SAT;
              break;

            case z3::unsat:
              *status = triton::engines::solver::UNSAT;
              break;

            case z3::unknown:
              if (solver.reason_unknown() == "timeout") {
                *status = triton::engines::solver::TIMEOUT;
              }
              else if (solver.reason_unknown() == "max. memory exceeded") {
                *status = triton::engines::solver::OUTOFMEM;
              }
              else {
                *status = triton::engines::solver::UNKNOWN;
              }
              break;
          }
        }
      }


      std::string Z3Solver::getName(void) const {
        return "z3";
      }


      void Z3Solver::setTimeout(triton::uint32 ms) {
        this->timeout = ms;
      }


      void Z3Solver::setMemoryLimit(triton::uint32 limit) {
        this->memoryLimit = limit;
      }

    };
  };
};
