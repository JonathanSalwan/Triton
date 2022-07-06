//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_PATHCONSTRAINT_H
#define TRITON_PATHCONSTRAINT_H

#include <string>
#include <tuple>
#include <vector>

#include <triton/ast.hpp>
#include <triton/dllexport.hpp>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Engines namespace
  namespace engines {
  /*!
   *  \ingroup triton
   *  \addtogroup engines
   *  @{
   */

    //! The Symbolic Execution namespace
    namespace symbolic {
    /*!
     *  \ingroup engines
     *  \addtogroup symbolic
     *  @{
     */

      /*! \class PathConstraint
          \brief The path constraint class. */
      class PathConstraint {
        protected:
          /*!
           * \brief The branches constraints
           * \details Vector of `<flag, source addr, dst addr, pc>`, `flag` is set to true if the branch is taken according the concrete
           * execution. The source address is the location of the branch instruction and the destination address is the destination of the jump.
           * E.g: `"0x11223344: jne 0x55667788"`, 0x11223344 is the source address and 0x55667788 is the destination if and only if the
           * branch is taken, otherwise the destination is the next instruction address. The SharedAbstractNode is the expression which need to be
           * true to take the branch.
           */
          std::vector<std::tuple<bool, triton::uint64, triton::uint64, triton::ast::SharedAbstractNode>> branches;

          //! The thread id of the constraint. -1 if it's undefined.
          triton::uint32 tid;

          //! The comment of the path constraint.
          std::string comment;

        public:
          //! Constructor.
          TRITON_EXPORT PathConstraint();

          //! Constructor by copy.
          TRITON_EXPORT PathConstraint(const PathConstraint &other);

          //! Destructor.
          TRITON_EXPORT ~PathConstraint();

          //! Operator.
          TRITON_EXPORT PathConstraint& operator=(const PathConstraint &other);

          //! Adds a branch to the path constraint.
          TRITON_EXPORT void addBranchConstraint(bool taken, triton::uint64 srdAddr, triton::uint64 dstAddr, const triton::ast::SharedAbstractNode& pc);

          //! Returns the branch constraints.
          TRITON_EXPORT const std::vector<std::tuple<bool, triton::uint64, triton::uint64, triton::ast::SharedAbstractNode>>& getBranchConstraints(void) const;

          //! Returns the address of the taken branch.
          TRITON_EXPORT triton::uint64 getTakenAddress(void) const;

          //! Returns the address of the jump instruction (eg.: "A: jz B", returns A).
          TRITON_EXPORT triton::uint64 getSourceAddress(void) const;

          //! Returns the predicate of the taken branch.
          TRITON_EXPORT triton::ast::SharedAbstractNode getTakenPredicate(void) const;

          //! Returns true if it is not a direct jump.
          TRITON_EXPORT bool isMultipleBranches(void) const;

          //! Returns the thread id of the constraint. Returns -1 if thread id is undefined.
          TRITON_EXPORT triton::uint32 getThreadId(void) const;

          //! Sets the thread id of the constraint.
          TRITON_EXPORT void setThreadId(triton::uint32 tid);

          //! Returns the comment of the path constraint.
          TRITON_EXPORT const std::string& getComment(void) const;

          //! Sets a comment to the path constraint.
          TRITON_EXPORT void setComment(const std::string& comment);
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PATHCONSTAINT_H */
