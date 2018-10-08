//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PATHMANAGER_H
#define TRITON_PATHMANAGER_H

#include <vector>

#include <triton/dllexport.hpp>
#include <triton/instruction.hpp>
#include <triton/modes.hpp>
#include <triton/pathConstraint.hpp>
#include <triton/symbolicExpression.hpp>
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

      /*! \class PathManager
          \brief The path manager class. */
      class PathManager {
        private:
          //! Modes API.
          triton::modes::Modes& modes;

          //! AstContext API
          triton::ast::AstContext& astCtxt;

        protected:
          //! \brief The logical conjunction vector of path constraints.
          std::vector<triton::engines::symbolic::PathConstraint> pathConstraints;

        public:
          //! Constructor.
          TRITON_EXPORT PathManager(triton::modes::Modes& modes, triton::ast::AstContext& astCtxt);

          //! Constructor by copy.
          TRITON_EXPORT PathManager(const PathManager& other);

          //! Copies a PathManager.
          TRITON_EXPORT PathManager& operator=(const PathManager& other);

          //! Returns the logical conjunction vector of path constraints.
          TRITON_EXPORT const std::vector<triton::engines::symbolic::PathConstraint>& getPathConstraints(void) const;

          //! Returns the logical conjunction AST of path constraints.
          TRITON_EXPORT triton::ast::SharedAbstractNode getPathConstraintsAst(void) const;

          //! Returns the number of constraints.
          TRITON_EXPORT triton::usize getNumberOfPathConstraints(void) const;

          //! Adds a path constraint.
          TRITON_EXPORT void addPathConstraint(const triton::arch::Instruction& inst, const triton::engines::symbolic::SharedSymbolicExpression& expr);

          //! Clears the logical conjunction vector of path constraints.
          TRITON_EXPORT void clearPathConstraints(void);
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PATHMANAGER_H */
