//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_PATHCONSTRAINT_H
#define TRITON_PATHCONSTRAINT_H

#include <tuple>
#include <vector>

#include "ast.hpp"
#include "tritonTypes.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Engines namespace
  namespace engines {
  /*!
   *  \ingroup triton
   *  \addtogroup engines
   *  @{
   */

    //! \module The Symbolic Execution namespace
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
           *  \brief The branches constraints
           *  \description Vector of `<flag, target bb addr, pc>`, `flag` is set to true if the branch is taken according the pc.
           */
          std::vector<std::tuple<bool, triton::__uint, triton::ast::AbstractNode*>> branches;


        public:
          //! Constructor.
          PathConstraint();

          //! Constructor by copy.
          PathConstraint(const PathConstraint &copy);

          //! Destructore.
          ~PathConstraint();

          //! Adds a branch to the path constraint.
          void addBranchConstraint(bool taken, triton::__uint bbAddr, triton::ast::AbstractNode* pc);

          //! Returns the branch constraints.
          const std::vector<std::tuple<bool, triton::__uint, triton::ast::AbstractNode*>>& getBranchConstraints(void) const;

          //! Returns the address of the taken branch.
          triton::__uint getTakenAddress(void) const;

          //! Returns the path constraint AST of the taken branch.
          triton::ast::AbstractNode* getTakenPathConstraintAst(void) const;

          //! Returns true if it is not a direct jump.
          bool isMultipleBranches(void) const;
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PATHCONSTAINT_H */

