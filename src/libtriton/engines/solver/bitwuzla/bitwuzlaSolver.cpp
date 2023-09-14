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
#include <triton/tritonToBitwuzla.hpp>
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

        // Count elapsed time.
        auto delta = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now() - p->start).count();

        // Check timeout expired.
        if (p->timeout && delta > p->timeout) {
          p->status = triton::engines::solver::TIMEOUT;
          return 1;
        }

        // Check memory limit.
        #if defined(__unix__)

        // Complete seconds elapsed from the start of solving.
        auto delta_s = delta / 1000;

        // Check memory limit every second. Don't perform check in first 100ms of solving.
        if (p->memory_limit && delta > 100 && delta_s > p->last_mem_check) {
          p->last_mem_check = delta_s;

          // Parse system file to get current process memory consumption (VmRSS field).
          size_t memory_usage = 0;
          std::ifstream str("/proc/self/status");
          if (str.is_open()) {
            std::string line;
            static std::regex vmsize("VmRSS:\\s*([0-9]+)\\s*kB");
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
            p->status = triton::engines::solver::OUTOFMEM;
            return 1;
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
        auto bzlaOptions = bitwuzla_options_new();
        bitwuzla_set_option(bzlaOptions, BITWUZLA_OPT_PRODUCE_MODELS, 1);
        auto bzla = bitwuzla_new(bzlaOptions);

        // Convert Triton' AST to solver terms.
        auto bzlaAst = triton::ast::TritonToBitwuzla();
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
          std::vector<BitwuzlaTerm> solution;
          solution.reserve(bzlaAst.getVariables().size());

          // Parse model.
          std::unordered_map<triton::usize, SolverModel> model;
          for (const auto& it : bzlaAst.getVariables()) {
            const char* svalue = bitwuzla_term_value_get_str_fmt(bitwuzla_get_value(bzla, it.first), 2);
            auto value = this->fromBvalueToUint512(svalue);
            auto m = SolverModel(it.second, value);
            model[m.getId()] = m;

            // Negate current model to escape duplication in the next solution.
            const auto& symvar_sort = bzlaAst.getBitvectorSorts().at(it.second->getSize());
            auto cur_val = bitwuzla_mk_bv_value(symvar_sort, svalue, 2);
            auto n = bitwuzla_mk_term2(BITWUZLA_KIND_EQUAL, it.first, cur_val);
            solution.push_back(bitwuzla_mk_term1(BITWUZLA_KIND_NOT, n));
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
              bitwuzla_assert(bzla, bitwuzla_mk_term(BITWUZLA_KIND_OR, solution.size(), solution.data()));
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
        bitwuzla_options_delete(bzlaOptions);

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


      triton::uint512 BitwuzlaSolver::evaluate(const triton::ast::SharedAbstractNode& node) const {
        if (node == nullptr) {
          throw triton::exceptions::AstLifting("BitwuzlaSolver::evaluate(): node cannot be null.");
        }

        auto bzlaOptions = bitwuzla_options_new();
        bitwuzla_set_option(bzlaOptions, BITWUZLA_OPT_PRODUCE_MODELS, 1);
        auto bzla = bitwuzla_new(bzlaOptions);

        // Query check-sat on empty solver to put Bitwuzla in SAT-state. Thus, it should be able to evaluate concrete formulas.
        if (bitwuzla_check_sat(bzla) != BITWUZLA_SAT) {
          bitwuzla_delete(bzla);
          bitwuzla_options_delete(bzlaOptions);
          throw triton::exceptions::SolverEngine("BitwuzlaSolver::evaluate(): empty solver didn't return SAT.");
        }

        // Evaluate concrete AST in solver.
        auto bzlaAst = triton::ast::TritonToBitwuzla(true);
        auto term_value = bitwuzla_get_value(bzla, bzlaAst.convert(node, bzla));

        triton::uint512 res = 0;
        if (bitwuzla_term_is_bool(term_value)) {
          res = bitwuzla_term_value_get_bool(term_value);
        } else {
          res = triton::uint512{bitwuzla_term_value_get_str_fmt(term_value, 10)};
        }

        bitwuzla_delete(bzla);
        bitwuzla_options_delete(bzlaOptions);

        return res;
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

      triton::uint512 BitwuzlaSolver::fromBvalueToUint512(const char* value) const {
        triton::usize   len = strlen(value);
        triton::usize   pos = 0;
        triton::uint512 res = 0;

        // Convert short bitvector string directly.
        if (len <= 64) {
          return std::strtoull(value, 0, 2L);
        }

        // Convert long bitvector string by 64-bit chunks.
        while (pos < len) {
          triton::usize sublen = std::min(len - pos, (triton::usize) 64UL);
          char* substr = new char[sublen + 1];
          std::memcpy(substr, value + pos, sublen);
          substr[sublen] = '\0';
          res = (res << sublen) + std::strtoull(substr, 0, 2L);
          pos += sublen;
          delete[] substr;
        }

        return res;
      }

    };
  };
};
