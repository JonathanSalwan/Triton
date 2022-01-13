//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <fstream>
#include <regex>
#include <string>

#include <triton/astContext.hpp>
#include <triton/bitwuzlaSolver.hpp>
#include <triton/exceptions.hpp>
#include <triton/solverModel.hpp>
#include <triton/symbolicExpression.hpp>
#include <triton/symbolicVariable.hpp>
#include <triton/tritonToBitwuzlaAst.hpp>
#include <triton/tritonTypes.hpp>


namespace triton {
  namespace engines {
    namespace solver {

      BitwuzlaSolver::BitwuzlaSolver() {
        this->timeout = 0;
        this->memoryLimit = 0;

        // Set bitwuzla abort function.
        bitwuzla_set_abort_callback(this->abortCallback);
      }


      int32_t BitwuzlaSolver::terminateCallback(void* state) {
        auto p = reinterpret_cast<SolverParams*>(state);

        // Execute this callback only once in every 1000 calls.
        if (++p->call_cnt < 1000) {
          return 0;
        }
        p->call_cnt = 0;

        // Count delta.
        auto delta = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now() - p->start).count();

        // Check timeout expired.
        if (p->timeout && delta > p->timeout) {
          p->code = triton::engines::solver::TIMEOUT;
          return 1;
        }

        // Check memory limit exceeded.
        #if defined(__unix__)
        // Conver delta to seconds, check memory limit every delay seconds.
        delta /= 1000;
        if (p->memory_limit && delta > p->last_mem_check && delta % p->delay == 0) {
          p->last_mem_check = delta;

          // Parse system file to get current process memory consumption (VmRSS field).
          size_t memory_usage = 0;
          std::ifstream str("/proc/self/status");
          if (str.is_open()) {
            std::string line;
            std::regex vmsize("VmRSS:\\s*([0-9]+)\\s*kB");
            while (std::getline(str, line)) {
              std::smatch match;
              if (std::regex_match(line, match, vmsize)) {
                memory_usage = strtoul(match.str(1).c_str(), NULL, 10) / 1024;
                break;
              }
            }
          }
          if (!memory_usage) {
            return 0;
          }
          if (memory_usage > p->memory_limit) {
            p->code = triton::engines::solver::OUTOFMEM;
            return 1;
          }
          // Since memory checking is not a free operation, we should
          // perform it as rarely as possible. We set delay according to
          // the occupied memory space relatively to the limit:
          //  - if we occupy <25% of limit check memory every 5s
          //  - if we occupy up to 75% of limit check memory every 2s
          //  - otherwise check memory every second
          if (memory_usage < p->memory_limit / 4) {
            p->delay = 5;
          }
          else if (memory_usage < 3 * p->memory_limit / 4) {
            p->delay = 2;
          }
          else {
            p->delay = 1;
          }
        }
        #endif

        return 0;
      }


      void BitwuzlaSolver::abortCallback(const char* msg) {
        throw triton::exceptions::SolverEngine(msg);
      }


      std::vector<std::unordered_map<triton::usize, SolverModel>> BitwuzlaSolver::getModels(const triton::ast::SharedAbstractNode& node,
                                                                                            triton::uint32 limit,
                                                                                            triton::engines::solver::status_e* status,
                                                                                            triton::uint32 timeout,
                                                                                            triton::uint32* solvingTime) const {
        if (node == nullptr)
          throw triton::exceptions::SolverEngine("BitwuzlaSolver::getModels(): Node cannot be null.");

        if (node->isLogical() == false)
          throw triton::exceptions::SolverEngine("BitwuzlaSolver::getModels(): Must be a logical node.");

        // Create solver.
        auto bzla = bitwuzla_new();
        bitwuzla_set_option(bzla, BITWUZLA_OPT_PRODUCE_MODELS, 1);
        if (limit > 1) {
          bitwuzla_set_option(bzla, BITWUZLA_OPT_INCREMENTAL, 1);
        }

        // Convert Triton' AST to solver terms.
        auto bzlaAst = triton::ast::TritonToBitwuzlaAst();
        bitwuzla_assert(bzla, bzlaAst.convert(node, bzla));

        // Set solving params.
        SolverParams p(this->timeout, this->memoryLimit);
        if (this->timeout || this->memoryLimit) {
          bitwuzla_set_termination_callback(bzla, this->terminateCallback, reinterpret_cast<void*>(&p));
        }

        // Get time of solving start.
        auto start = std::chrono::system_clock::now();

        // Check result.
        auto res = bitwuzla_check_sat(bzla);

        // Write back status.
        if (status) {
          switch (res) {
            case BITWUZLA_SAT:
              *status = triton::engines::solver::SAT;
              break;
            case BITWUZLA_UNSAT:
              *status = triton::engines::solver::UNSAT;
              break;
            case BITWUZLA_UNKNOWN:
              *status = p.status;
              break;
          }
        }

        std::vector<std::unordered_map<triton::usize, SolverModel>> ret;
        while(res == BITWUZLA_SAT && limit >= 1) {
          std::vector<const BitwuzlaTerm*> solution;
          solution.reserve(bzlaAst.getVariables().size());

          // Parse model.
          std::unordered_map<triton::usize, SolverModel> model;
          for (const auto& it : bzlaAst.getVariables()) {
            const char* svalue = bitwuzla_get_bv_value(bzla, it.first);
            triton::uint512 value = strtoull(svalue, 0, 2L);
            auto m = SolverModel(it.second, value);
            model[m.getId()] = m;

            // Negate current model to escape duplication in the next solution.
            const auto& symvar_sort = bzlaAst.getBitvectorSorts().at(it.second->getSize());
            auto cur_val = bitwuzla_mk_bv_value(bzla, symvar_sort, svalue, BITWUZLA_BV_BASE_BIN);
            auto n = bitwuzla_mk_term2(bzla, BITWUZLA_KIND_EQUAL, it.first, cur_val);
            solution.push_back(bitwuzla_mk_term1(bzla, BITWUZLA_KIND_NOT, n));
          }

          // Check that model is available.
          if (model.empty()) {
            break;
          }

          // Push model.
          ret.push_back(model);

          if (--limit) {
            // Escape last model.
            if (solution.size() > 1) {
              bitwuzla_assert(bzla, bitwuzla_mk_term(bzla, BITWUZLA_KIND_OR, solution.size(), solution.data()));
            }
            else {
              bitwuzla_assert(bzla, solution.front());
            }

            // Get next model.
            res = bitwuzla_check_sat(bzla);
          }
        }

        // Get time of solving end.
        auto end = std::chrono::system_clock::now();

        if (solvingTime)
          *solvingTime = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();

        bitwuzla_delete(bzla);

        return ret;
      }


      bool BitwuzlaSolver::isSat(const triton::ast::SharedAbstractNode& node, triton::engines::solver::status_e* status, triton::uint32 timeout, triton::uint32* solvingTime) const {
        triton::engines::solver::status_e st;

        this->getModels(node, 0, &st, timeout, solvingTime);

        if (status) {
          *status = st;
        }
        return st == triton::engines::solver::SAT;
      }


      std::unordered_map<triton::usize, SolverModel> BitwuzlaSolver::getModel(const triton::ast::SharedAbstractNode& node, triton::engines::solver::status_e* status, triton::uint32 timeout, triton::uint32* solvingTime) const {
        auto models = this->getModels(node, 1, status, timeout, solvingTime);
        return models.empty() ? std::unordered_map<triton::usize, SolverModel>() : models.front();
      }


      std::string BitwuzlaSolver::getName(void) const {
        return "Bitwuzla";
      }


      void BitwuzlaSolver::setTimeout(triton::uint32 ms) {
        this->timeout = ms;
      }


      void BitwuzlaSolver::setMemoryLimit(triton::uint32 limit) {
        this->memoryLimit = limit;
      }

    };
  };
};
