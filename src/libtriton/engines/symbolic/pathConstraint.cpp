//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/pathConstraint.hpp>



namespace triton {
  namespace engines {
    namespace symbolic {

      PathConstraint::PathConstraint() {
      }


      PathConstraint::PathConstraint(const PathConstraint &copy) {
        this->branches = copy.branches;
      }


      PathConstraint::~PathConstraint() {
      }


      void PathConstraint::addBranchConstraint(bool taken, triton::uint64 srcAddr, triton::uint64 dstAddr, triton::ast::AbstractNode* pc) {
        if (pc == nullptr)
          throw triton::exceptions::PathConstraint("PathConstraint::addBranchConstraint(): The PC node cannot be null.");
        this->branches.push_back(std::make_tuple(taken, srcAddr, dstAddr, pc));
      }


      const std::vector<std::tuple<bool, triton::uint64, triton::uint64, triton::ast::AbstractNode*>>& PathConstraint::getBranchConstraints(void) const {
        return this->branches;
      }


      triton::uint64 PathConstraint::getTakenAddress(void) const {
        for (auto it = this->branches.begin(); it != this->branches.end(); it++) {
          if (std::get<0>(*it) == true)
            return std::get<2>(*it);
        }
        throw triton::exceptions::PathConstraint("PathConstraint::getTakenAddress(): Something wrong, no branch taken.");
      }


      triton::ast::AbstractNode* PathConstraint::getTakenPathConstraintAst(void) const {
        for (auto it = this->branches.begin(); it != this->branches.end(); it++) {
          if (std::get<0>(*it) == true)
            return std::get<3>(*it);
        }
        throw triton::exceptions::PathConstraint("PathConstraint::getTakenPathConstraintAst(): Something wrong, no branch taken.");
      }


      bool PathConstraint::isMultipleBranches(void) const {
        if (this->branches.size() == 0)
          throw triton::exceptions::PathConstraint("PathConstraint::isMultipleBranches(): Path Constraint is empty.");
        else if (this->branches.size() == 1)
          return false;
        return true;
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

