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

      PathManager::PathManager(const triton::modes::SharedModes& modes, const triton::ast::SharedAstContext& astCtxt)
        : modes(modes), astCtxt(astCtxt) {
      }


      PathManager::PathManager(const PathManager& other)
        : modes(other.modes), astCtxt(other.astCtxt) {
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


      /* Returns the current path predicate as an AST of logical conjunction of each taken branch. */
      triton::ast::SharedAbstractNode PathManager::getPathPredicate(void) const {
        std::vector<triton::engines::symbolic::PathConstraint>::const_iterator it;

        /* by default PC is T (top) */
        auto node = this->astCtxt->equal(
                      this->astCtxt->bvtrue(),
                      this->astCtxt->bvtrue()
                    );

        /* Then, we create a conjunction of path constraint */
        for (it = this->pathConstraints.begin(); it != this->pathConstraints.end(); it++) {
          node = this->astCtxt->land(node, it->getTakenPredicate());
        }

        return node;
      }



      std::vector<triton::ast::SharedAbstractNode> PathManager::getPredicatesToReachAddress(triton::uint64 addr) const {
        std::vector<triton::ast::SharedAbstractNode> predicates;

        /* by default PC is T (top) */
        auto node = this->astCtxt->equal(
                      this->astCtxt->bvtrue(),
                      this->astCtxt->bvtrue()
                    );

        /* Go through all path constraints */
        for (auto pc = this->pathConstraints.begin(); pc != this->pathConstraints.end(); pc++) {
          auto branches = pc->getBranchConstraints();
          bool isMultib = (branches.size() >= 2);

          /* Check if one of the branch constraint may reach the targeted address */
          for (auto branch = branches.begin(); branch != branches.end(); branch++) {
            /* if source branch == target, add the current path predicate */
            if (std::get<1>(*branch) == addr) {
              predicates.push_back(node);
            }
            /*
             * if dst branch == target, do the conjunction of the current
             * path predicate and the branch constraint.
             */
            if (std::get<2>(*branch) == addr) {
              predicates.push_back(this->astCtxt->land(node, std::get<3>(*branch)));
            }
            /*
             * if it's a direct branch (call reg, jmp reg) and not a standalone
             * constraint. Try to reach the targeted address.
             */
            if (isMultib == false && std::get<1>(*branch) != 0 && std::get<2>(*branch) != 0) {
              if (std::get<3>(*branch)->getType() == triton::ast::EQUAL_NODE) {
                auto ip = std::get<3>(*branch)->getChildren()[0];
                predicates.push_back(this->astCtxt->land(node, this->astCtxt->equal(ip, this->astCtxt->bv(addr, ip->getBitvectorSize()))));
              }
            }
          } /* branch constraints */

          /* Continue to create the conjunction of the current path predicate */
          node = this->astCtxt->land(node, pc->getTakenPredicate());
        } /* path constraint */

        return predicates;
      }


      /* Pushs constraints of a branch instruction to the path predicate. */
      void PathManager::pushPathConstraint(const triton::arch::Instruction& inst, const triton::engines::symbolic::SharedSymbolicExpression& expr) {
        triton::engines::symbolic::PathConstraint pco;
        triton::uint64 srcAddr = 0;
        triton::uint64 dstAddr = 0;
        triton::uint32 size    = 0;

        triton::ast::SharedAbstractNode pc = expr->getAst();
        if (pc == nullptr)
          throw triton::exceptions::PathManager("PathManager::pushPathConstraint(): The node cannot be null.");

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
          throw triton::exceptions::PathManager("PathManager::pushPathConstraint(): The node size cannot be zero.");

        if (pc->getType() == triton::ast::ZX_NODE)
          pc = pc->getChildren()[1];

        /* Multiple branches */
        if (pc->getType() == triton::ast::ITE_NODE) {
          triton::uint64 bb1 = pc->getChildren()[1]->evaluate().convert_to<triton::uint64>();
          triton::uint64 bb2 = pc->getChildren()[2]->evaluate().convert_to<triton::uint64>();

          triton::ast::SharedAbstractNode bb1pc = (bb1 == dstAddr) ? this->astCtxt->equal(pc, this->astCtxt->bv(dstAddr, size)) :
                                                                     this->astCtxt->lnot(this->astCtxt->equal(pc, this->astCtxt->bv(dstAddr, size)));

          triton::ast::SharedAbstractNode bb2pc = (bb2 == dstAddr) ? this->astCtxt->equal(pc, this->astCtxt->bv(dstAddr, size)) :
                                                                     this->astCtxt->lnot(this->astCtxt->equal(pc, this->astCtxt->bv(dstAddr, size)));
          /* Branch A */
          pco.addBranchConstraint(
            bb1 == dstAddr, /* is taken ? */
            srcAddr,        /* from       */
            bb1,            /* to         */
            bb1pc           /* expr which must be true to take the branch */
          );

          /* Branch B */
          pco.addBranchConstraint(
            bb2 == dstAddr, /* is taken ? */
            srcAddr,        /* from       */
            bb2,            /* to         */
            bb2pc           /* expr which must be true to take the branch */
          );

          this->pathConstraints.push_back(pco);
        }

        /* Direct branch */
        else {
          pco.addBranchConstraint(
            true,     /* always taken */
            srcAddr,  /* from */
            dstAddr,  /* to */
            /* expr which must be true to take the branch */
            this->astCtxt->equal(pc, this->astCtxt->bv(dstAddr, size))
          );
          this->pathConstraints.push_back(pco);
        }
      }


      /* Pushs constraints to the current path predicate. */
      void PathManager::pushPathConstraint(const triton::ast::SharedAbstractNode& node) {
        triton::engines::symbolic::PathConstraint pco;

        if (node->isLogical() == false)
          throw triton::exceptions::PathManager("PathManager::pushPathConstraint(): The node must be a logical node.");

        pco.addBranchConstraint(
          true, /* always taken   */
          0,    /* from: not used */
          0,    /* to: not used   */
          node  /* expr which must be true to take the branch */
        );

        this->pathConstraints.push_back(pco);
      }


      /* Pops the last constraints added to the path predicate. */
      void PathManager::popPathConstraint(void) {
        if (this->pathConstraints.size())
          this->pathConstraints.pop_back();
      }


      /* Clears the current path predicate. */
      void PathManager::clearPathConstraints(void) {
        this->pathConstraints.clear();
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */
