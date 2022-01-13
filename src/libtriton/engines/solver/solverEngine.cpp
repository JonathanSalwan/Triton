//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/config.hpp>
#include <triton/exceptions.hpp>
#include <triton/solverEngine.hpp>



namespace triton {
  namespace engines {
    namespace solver {

      SolverEngine::SolverEngine() {
        this->kind = triton::engines::solver::SOLVER_INVALID;
        #if defined(TRITON_Z3_INTERFACE)
        /* By default we initialized the z3 solver */
        this->setSolver(triton::engines::solver::SOLVER_Z3);
        #elif defined(TRITON_BITWUZLA_INTERFACE)
        this->setSolver(triton::engines::solver::SOLVER_BITWUZLA);
        #endif
      }


      triton::engines::solver::solver_e SolverEngine::getSolver(void) const {
        return this->kind;
      }


      const triton::engines::solver::SolverInterface* SolverEngine::getSolverInstance(void) const {
        if (!this->solver)
          throw triton::exceptions::SolverEngine("SolverEngine::getSolver(): Solver undefined.");
        return this->solver.get();
      }


      void SolverEngine::setSolver(triton::engines::solver::solver_e kind) {
        /* Allocate and init the good solver */
        switch (kind) {
          #ifdef TRITON_Z3_INTERFACE
          case triton::engines::solver::SOLVER_Z3:
            /* init the new instance */
            this->solver.reset(new(std::nothrow) triton::engines::solver::Z3Solver());
            if (this->solver == nullptr)
              throw triton::exceptions::SolverEngine("SolverEngine::setSolver(): Not enough memory.");
            break;
          #endif
          #ifdef TRITON_BITWUZLA_INTERFACE
          case triton::engines::solver::SOLVER_BITWUZLA:
            /* init the new instance */
            this->solver.reset(new(std::nothrow) triton::engines::solver::BitwuzlaSolver());
            if (this->solver == nullptr)
              throw triton::exceptions::SolverEngine("SolverEngine::setSolver(): Not enough memory.");
            break;
          #endif

          default:
            throw triton::exceptions::SolverEngine("SolverEngine::setSolver(): Solver not supported.");
            break;
        }

        /* Setup global variables */
        this->kind = kind;
      }


      void SolverEngine::setCustomSolver(triton::engines::solver::SolverInterface* customSolver) {
        if (customSolver == nullptr)
          throw triton::exceptions::SolverEngine("SolverEngine::setCustomSolver(): custom solver cannot be null.");

        /* Define the custom solver as current solver */
        this->solver.reset(customSolver);

        /* Setup global variables */
        this->kind = triton::engines::solver::SOLVER_CUSTOM;
      }


      bool SolverEngine::isValid(void) const {
        if (this->kind == triton::engines::solver::SOLVER_INVALID)
          return false;
        return true;
      }


      std::unordered_map<triton::usize, SolverModel> SolverEngine::getModel(const triton::ast::SharedAbstractNode& node, triton::engines::solver::status_e* status, triton::uint32 timeout, triton::uint32* solvingTime) const {
        if (!this->solver)
          return std::unordered_map<triton::usize, SolverModel>{};
        return this->solver->getModel(node, status, timeout, solvingTime);
      }


      std::vector<std::unordered_map<triton::usize, SolverModel>> SolverEngine::getModels(const triton::ast::SharedAbstractNode& node, triton::uint32 limit, triton::engines::solver::status_e* status, triton::uint32 timeout, triton::uint32* solvingTime) const {
        if (!this->solver)
          return std::vector<std::unordered_map<triton::usize, SolverModel>>{};
        return this->solver->getModels(node, limit, status, timeout, solvingTime);
      }


      bool SolverEngine::isSat(const triton::ast::SharedAbstractNode& node, triton::engines::solver::status_e* status, triton::uint32 timeout, triton::uint32* solvingTime) const {
        if (!this->solver)
          return false;
        return this->solver->isSat(node, status, timeout, solvingTime);
      }


      std::string SolverEngine::getName(void) const {
        if (!this->solver)
          return "n/a";
        return this->solver->getName();
      }


      void SolverEngine::setTimeout(triton::uint32 ms) {
        if (this->solver) {
          this->solver->setTimeout(ms);
        }
      }


      void SolverEngine::setMemoryLimit(triton::uint32 limit) {
        if (this->solver) {
          this->solver->setMemoryLimit(limit);
        }
      }

    };
  };
};
