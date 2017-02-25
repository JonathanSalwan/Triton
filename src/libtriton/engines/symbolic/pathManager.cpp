//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/pathManager.hpp>
#include <triton/symbolicEnums.hpp>



namespace triton {
  namespace engines {
    namespace symbolic {

      PathManager::PathManager(triton::modes::Modes* modes) {
        if (modes == nullptr)
          throw triton::exceptions::PathManager("PathManager::PathManager(): The modes API cannot be null.");
        this->modes = modes;
      }


      PathManager::PathManager(const PathManager& copy) {
        this->copy(copy);
      }


      PathManager::~PathManager() {
      }


      void PathManager::copy(const PathManager& other) {
        this->modes           = other.modes;
        this->pathConstraints = other.pathConstraints;
      }


      /* Returns the logical conjunction vector of path constraint */
      const std::vector<triton::engines::symbolic::PathConstraint>& PathManager::getPathConstraints(void) const {
        return this->pathConstraints;
      }


      /* Returns the logical conjunction AST of path constraint */
      triton::ast::AbstractNode* PathManager::getPathConstraintsAst(void) const {
        std::vector<triton::engines::symbolic::PathConstraint>::const_iterator it;
        triton::ast::AbstractNode* node = nullptr;

        /* by default PC is T (top) */
        node = triton::ast::equal(
                 triton::ast::bvtrue(),
                 triton::ast::bvtrue()
               );

        /* Then, we create a conjunction of pc */
        for (it = this->pathConstraints.begin(); it != this->pathConstraints.end(); it++) {
          node = triton::ast::land(node, it->getTakenPathConstraintAst());
        }

        return node;
      }


      triton::usize PathManager::getNumberOfPathConstraints(void) const {
        return this->pathConstraints.size();
      }


      /* Add a path constraint */
      void PathManager::addPathConstraint(const triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* expr) {
        triton::engines::symbolic::PathConstraint pco;
        triton::ast::AbstractNode* pc = nullptr;
        triton::uint64 srcAddr        = 0;
        triton::uint64 dstAddr        = 0;
        triton::uint32 size           = 0;

        pc = expr->getAst();
        if (pc == nullptr)
          throw triton::exceptions::PathManager("PathManager::addPathConstraint(): The PC node cannot be null.");

        /* If PC_TRACKING_SYMBOLIC is enabled, Triton will track path constraints only if they are symbolized. */
        if (this->modes->isModeEnabled(triton::modes::PC_TRACKING_SYMBOLIC) && !pc->isSymbolized())
          return;

        /* If ONLY_ON_TAINTED is enabled and the expression untainted, Triton will skip the storing process. */
        if (this->modes->isModeEnabled(triton::modes::ONLY_ON_TAINTED) && !expr->isTainted)
          return;

        /* Basic block taken */
        srcAddr = inst.getAddress();
        dstAddr = pc->evaluate().convert_to<triton::uint64>();
        size    = pc->getBitvectorSize();

        if (size == 0)
          throw triton::exceptions::PathManager("PathManager::addPathConstraint(): The PC node size cannot be zero.");

        if (pc->getKind() == triton::ast::ZX_NODE)
          pc = pc->getChilds()[1];

        /* Multiple branches */
        if (pc->getKind() == triton::ast::ITE_NODE) {
          triton::uint64 bb1 = pc->getChilds()[1]->evaluate().convert_to<triton::uint64>();
          triton::uint64 bb2 = pc->getChilds()[2]->evaluate().convert_to<triton::uint64>();

          triton::ast::AbstractNode* bb1pc = (bb1 == dstAddr) ? triton::ast::equal(pc, triton::ast::bv(dstAddr, size)) :
                                                                triton::ast::lnot(triton::ast::equal(pc, triton::ast::bv(dstAddr, size)));

          triton::ast::AbstractNode* bb2pc = (bb2 == dstAddr) ? triton::ast::equal(pc, triton::ast::bv(dstAddr, size)) :
                                                                triton::ast::lnot(triton::ast::equal(pc, triton::ast::bv(dstAddr, size)));

          pco.addBranchConstraint(bb1 == dstAddr, srcAddr, bb1, bb1pc);
          pco.addBranchConstraint(bb2 == dstAddr, srcAddr, bb2, bb2pc);

          this->pathConstraints.push_back(pco);
        }

        /* Direct branch */
        else {
          pco.addBranchConstraint(true, srcAddr, dstAddr, triton::ast::equal(pc, triton::ast::bv(dstAddr, size)));
          this->pathConstraints.push_back(pco);
        }

      }


      void PathManager::clearPathConstraints(void) {
        this->pathConstraints.clear();
      }


      void PathManager::operator=(const PathManager& other) {
        this->copy(other);
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

