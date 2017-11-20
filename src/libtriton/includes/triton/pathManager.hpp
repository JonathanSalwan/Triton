//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PATHMANAGER_H
#define TRITON_PATHMANAGER_H

#include <vector>

#include <triton/astContext.hpp>
#include <triton/instruction.hpp>
#include <triton/modes.hpp>
#include <triton/pathConstraint.hpp>
#include <triton/symbolicExpression.hpp>
#include <tritoncore/types.hpp>



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

      /*! \class PathManager
          \brief The path manager class. */
      class PathManager {
        private:
          //! Modes API.
          const triton::modes::Modes& modes;

          //! Context API
          triton::AstContext & astCtxt;

        protected:
          //! \brief The logical conjunction vector of path constraints.
          std::vector<triton::engines::symbolic::PathConstraint> pathConstraints;

        public:
          //! Constructor.
          PathManager(const triton::modes::Modes& modes, triton::AstContext& astCtxt);

          //! Constructor by copy.
          PathManager(const PathManager& copy);

          //! Copies a PathManager.
          void copy(const PathManager& other);

          //! Returns the logical conjunction vector of path constraints.
          const std::vector<triton::engines::symbolic::PathConstraint>& getPathConstraints(void) const;

          //! Returns the logical conjunction AST of path constraints.
          triton::ast::SharedAbstractNode getPathConstraintsAst(void) const;

          //! Returns the number of constraints.
          triton::usize getNumberOfPathConstraints(void) const;

          //! Adds a path constraint.
          void addPathConstraint(const triton::arch::Instruction& inst, triton::SharedSymbolicExpression const& expr);

          //! Clears the logical conjunction vector of path constraints.
          void clearPathConstraints(void);

          //! Copies a PathManager.
          void operator=(const PathManager& other);
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PATHMANAGER_H */

