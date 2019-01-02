//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/astContext.hpp>
#include <triton/exceptions.hpp>
#include <triton/pathManager.hpp>
#include <triton/symbolicEnums.hpp>



namespace triton {
  namespace engines {
    namespace symbolic {

      PathManager::PathManager(triton::modes::Modes& modes, triton::ast::AstContext& astCtxt)
        : modes(modes),
          astCtxt(astCtxt) {
      }


      PathManager::PathManager(const PathManager& other)
        : modes(other.modes),
          astCtxt(other.astCtxt) {
        this->pathConstraints = other.pathConstraints;
      }


      PathManager& PathManager::operator=(const PathManager& other) {
        this->astCtxt         = other.astCtxt;
        this->modes           = other.modes;
        this->pathConstraints = other.pathConstraints;
        return *this;
      }


      /* Returns the logical conjunction vector of path constraint */
      const std::vector<triton::engines::symbolic::PathConstraint>& PathManager::getPathConstraints(void) const {
        return this->pathConstraints;
      }


      /* Returns the logical conjunction AST of path constraint */
      triton::ast::SharedAbstractNode PathManager::getPathConstraintsAst(void) const {
        // Every constraint should have the same context otherwise, we can't know
        // which one to use for the current node computation.
        std::vector<triton::engines::symbolic::PathConstraint>::const_iterator it;

        /* by default PC is T (top) */
        auto node = this->astCtxt.equal(
                      this->astCtxt.bvtrue(),
                      this->astCtxt.bvtrue()
                    );

        /* Then, we create a conjunction of pc */
        for (it = this->pathConstraints.begin(); it != this->pathConstraints.end(); it++) {
          node = this->astCtxt.land(node, it->getTakenPathConstraintAst());
        }

        return node;
      }


      triton::usize PathManager::getNumberOfPathConstraints(void) const {
        return this->pathConstraints.size();
      }


      /* Add a path constraint */
      void PathManager::addPathConstraint(const triton::arch::Instruction& inst, const triton::engines::symbolic::SharedSymbolicExpression& expr) {
        triton::engines::symbolic::PathConstraint pco;
        triton::uint64 srcAddr = 0;
        triton::uint64 dstAddr = 0;
        triton::uint32 size    = 0;

        triton::ast::SharedAbstractNode pc = expr->getAst();
        if (pc == nullptr)
          throw triton::exceptions::PathManager("PathManager::addPathConstraint(): The PC node cannot be null.");

        /* If PC_TRACKING_SYMBOLIC is enabled, Triton will track path constraints only if they are symbolized. */
        if (this->modes.isModeEnabled(triton::modes::PC_TRACKING_SYMBOLIC) && !pc->isSymbolized())
          return;

        /* If ONLY_ON_TAINTED is enabled and the expression untainted, Triton will skip the storing process. */
        if (this->modes.isModeEnabled(triton::modes::ONLY_ON_TAINTED) && !expr->isTainted)
          return;

        /* Basic block taken */
        srcAddr = inst.getAddress();
        dstAddr = pc->evaluate().convert_to<triton::uint64>();
        size    = pc->getBitvectorSize();

        if (size == 0)
          throw triton::exceptions::PathManager("PathManager::addPathConstraint(): The PC node size cannot be zero.");

        if (pc->getType() == triton::ast::ZX_NODE)
          pc = pc->getChildren()[1];

        /* Multiple branches */
        if (pc->getType() == triton::ast::ITE_NODE) {
          triton::uint64 bb1 = pc->getChildren()[1]->evaluate().convert_to<triton::uint64>();
          triton::uint64 bb2 = pc->getChildren()[2]->evaluate().convert_to<triton::uint64>();

          triton::ast::SharedAbstractNode bb1pc = (bb1 == dstAddr) ? this->astCtxt.equal(pc, this->astCtxt.bv(dstAddr, size)) :
                                                                     this->astCtxt.lnot(this->astCtxt.equal(pc, this->astCtxt.bv(dstAddr, size)));

          triton::ast::SharedAbstractNode bb2pc = (bb2 == dstAddr) ? this->astCtxt.equal(pc, this->astCtxt.bv(dstAddr, size)) :
                                                                     this->astCtxt.lnot(this->astCtxt.equal(pc, this->astCtxt.bv(dstAddr, size)));

          pco.addBranchConstraint(bb1 == dstAddr, srcAddr, bb1, bb1pc);
          pco.addBranchConstraint(bb2 == dstAddr, srcAddr, bb2, bb2pc);

          this->pathConstraints.push_back(pco);
        }

        /* Direct branch */
        else {
          pco.addBranchConstraint(true, srcAddr, dstAddr, this->astCtxt.equal(pc, this->astCtxt.bv(dstAddr, size)));
          this->pathConstraints.push_back(pco);
        }

      }


      void PathManager::clearPathConstraints(void) {
        this->pathConstraints.clear();
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */
