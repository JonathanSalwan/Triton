//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/exceptions.hpp>
#include <triton/pathConstraint.hpp>



namespace triton {
  namespace engines {
    namespace symbolic {

      PathConstraint::PathConstraint() {
        this->tid = static_cast<triton::uint32>(-1);
      }


      PathConstraint::PathConstraint(const PathConstraint &other) {
        this->branches  = other.branches;
        this->comment   = other.comment;
        this->tid       = other.tid;
      }


      PathConstraint::~PathConstraint() {
        /* See #828: Release ownership before calling container destructor */
        this->branches.clear();
      }


      PathConstraint& PathConstraint::operator=(const PathConstraint &other) {
        this->branches  = other.branches;
        this->comment   = other.comment;
        this->tid       = other.tid;
        return *this;
      }


      void PathConstraint::addBranchConstraint(bool taken, triton::uint64 srcAddr, triton::uint64 dstAddr, const triton::ast::SharedAbstractNode& pc) {
        if (pc == nullptr)
          throw triton::exceptions::PathConstraint("PathConstraint::addBranchConstraint(): The PC node cannot be null.");
        this->branches.push_back(std::make_tuple(taken, srcAddr, dstAddr, pc));
      }


      const std::vector<std::tuple<bool, triton::uint64, triton::uint64, triton::ast::SharedAbstractNode>>& PathConstraint::getBranchConstraints(void) const {
        return this->branches;
      }


      triton::uint64 PathConstraint::getSourceAddress(void) const {
        for (auto it = this->branches.begin(); it != this->branches.end(); it++) {
          if (std::get<0>(*it) == true)
            return std::get<1>(*it);
        }
        throw triton::exceptions::PathConstraint("PathConstraint::getSourceAddress(): Something wrong, no branch.");
      }


      triton::uint64 PathConstraint::getTakenAddress(void) const {
        for (auto it = this->branches.begin(); it != this->branches.end(); it++) {
          if (std::get<0>(*it) == true)
            return std::get<2>(*it);
        }
        throw triton::exceptions::PathConstraint("PathConstraint::getTakenAddress(): Something wrong, no branch taken.");
      }


      triton::ast::SharedAbstractNode PathConstraint::getTakenPredicate(void) const {
        for (auto it = this->branches.begin(); it != this->branches.end(); it++) {
          if (std::get<0>(*it) == true)
            return std::get<3>(*it);
        }
        throw triton::exceptions::PathConstraint("PathConstraint::getTakenPredicate(): Something wrong, no branch taken.");
      }


      bool PathConstraint::isMultipleBranches(void) const {
        if (this->branches.size() == 0)
          throw triton::exceptions::PathConstraint("PathConstraint::isMultipleBranches(): Path Constraint is empty.");
        else if (this->branches.size() == 1)
          return false;
        return true;
      }


      triton::uint32 PathConstraint::getThreadId(void) const {
        return this->tid;
      }


      void PathConstraint::setThreadId(triton::uint32 tid) {
        this->tid = tid;
      }


      const std::string& PathConstraint::getComment(void) const {
        return this->comment;
      }


      void PathConstraint::setComment(const std::string& comment) {
        this->comment = comment;
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */
