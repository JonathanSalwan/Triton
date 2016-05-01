//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <pathConstraint.hpp>



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


      void PathConstraint::addBranchConstraint(bool taken, triton::__uint bbAddr, triton::ast::AbstractNode* pc) {
        if (pc == nullptr)
          throw std::runtime_error("PathConstraint::addBranchConstraint(): The PC node cannot be null.");
        this->branches.push_back(std::make_tuple(taken, bbAddr, pc));
      }


      const std::vector<std::tuple<bool, triton::__uint, triton::ast::AbstractNode*>>& PathConstraint::getBranchConstraints(void) const {
        return this->branches;
      }


      triton::__uint PathConstraint::getTakenAddress(void) const {
        for (auto it = this->branches.begin(); it != this->branches.end(); it++) {
          if (std::get<0>(*it) == true)
            return std::get<1>(*it);
        }
        throw std::runtime_error("PathConstraint::getTakenAddress(): Something wrong, no branch taken.");
      }


      triton::ast::AbstractNode* PathConstraint::getTakenPathConstraintAst(void) const {
        for (auto it = this->branches.begin(); it != this->branches.end(); it++) {
          if (std::get<0>(*it) == true)
            return std::get<2>(*it);
        }
        throw std::runtime_error("PathConstraint::getTakenPathConstraintAst(): Something wrong, no branch taken.");
      }


      bool PathConstraint::isMultipleBranches(void) const {
        if (this->branches.size() == 0)
          throw std::runtime_error("PathConstraint::isMultipleBranches(): Path Constraint is empty.");
        else if (this->branches.size() == 1)
          return false;
        return true;
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

