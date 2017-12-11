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
          const triton::modes::Modes& modes;

          //! AstContext API
          triton::ast::AstContext& astCtxt;

          //! Copies a PathManager.
          void copy(const PathManager& other);

        protected:
          //! \brief The logical conjunction vector of path constraints.
          std::vector<triton::engines::symbolic::PathConstraint> pathConstraints;

        public:
          //! Constructor.
          TRITON_EXPORT PathManager(const triton::modes::Modes& modes, triton::ast::AstContext& astCtxt);

          //! Constructor by copy.
          TRITON_EXPORT PathManager(const PathManager& other);

          //! Returns the logical conjunction vector of path constraints.
          TRITON_EXPORT const std::vector<triton::engines::symbolic::PathConstraint>& getPathConstraints(void) const;

          //! Returns the logical conjunction AST of path constraints.
          TRITON_EXPORT triton::ast::AbstractNode* getPathConstraintsAst(void) const;

          //! Returns the number of constraints.
          TRITON_EXPORT triton::usize getNumberOfPathConstraints(void) const;

          //! Adds a path constraint.
          TRITON_EXPORT void addPathConstraint(const triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* expr);

          //! Clears the logical conjunction vector of path constraints.
          TRITON_EXPORT void clearPathConstraints(void);

          //! Copies a PathManager.
          TRITON_EXPORT PathManager& operator=(const PathManager& other);
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PATHMANAGER_H */

