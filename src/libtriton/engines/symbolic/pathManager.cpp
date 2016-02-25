//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <pathManager.hpp>



namespace triton {
  namespace engines {
    namespace symbolic {

      PathManager::PathManager() {
      }


      PathManager::PathManager(const PathManager &copy) {
        this->pathConstraints = copy.pathConstraints;
      }


      PathManager::~PathManager() {
      }


      /* Returns the logical conjunction vector of path constraint */
      std::vector<triton::ast::AbstractNode*>& PathManager::getPathConstraints(void) {
        return this->pathConstraints;
      }


      /* Returns the logical conjunction AST of path constraint */
      triton::ast::AbstractNode* PathManager::getPathConstraintsAst(void) {
        triton::ast::AbstractNode* node = nullptr;
        std::vector<triton::ast::AbstractNode*>::iterator it;

        /* by default PC is T (top) */
        node = triton::ast::equal(
                 triton::ast::bvtrue(),
                 triton::ast::bvtrue()
               );

        /* Then, we create a conjunction of pc */
        for (it = this->pathConstraints.begin(); it != this->pathConstraints.end(); it++) {
          node = triton::ast::land(node, *it);
        }

        return node;
      }


      triton::uint32 PathManager::getNumberOfPathConstraints(void) {
        return this->pathConstraints.size();
      }


      /* Add a path constraint */
      void PathManager::addPathConstraint(triton::ast::AbstractNode* pc) {
        triton::uint128 value = 0;
        triton::uint32  size  = 0;

        if (pc == nullptr)
          throw std::runtime_error("SymbolicEngine::addPathConstraint(): The PC node cannot be null.");

        value = pc->evaluate().convert_to<triton::uint128>();
        size  = pc->getBitvectorSize();

        if (size == 0)
          throw std::runtime_error("SymbolicEngine::addPathConstraint(): The PC node size cannot be zero.");

        pc = triton::ast::equal(pc, triton::ast::bv(value, size));
        this->pathConstraints.push_back(pc);
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

