//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_PATHMANAGER_H
#define TRITON_PATHMANAGER_H

#include <vector>

#include "pathConstraint.hpp"
#include "symbolicExpression.hpp"
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

      /*! \class PathManager
          \brief The path manager class. */
      class PathManager {
        protected:
          //! \brief The logical conjunction vector of path constraints.
          std::vector<triton::engines::symbolic::PathConstraint> pathConstraints;


        public:
          //! Constructor.
          PathManager();

          //! Constructor by copy.
          PathManager(const PathManager &copy);

          //! Destructore.
          ~PathManager();

          //! Returns the logical conjunction vector of path constraints.
          const std::vector<triton::engines::symbolic::PathConstraint>& getPathConstraints(void) const;

          //! Returns the logical conjunction AST of path constraints.
          triton::ast::AbstractNode* getPathConstraintsAst(void) const;

          //! Returns the number of constraints.
          triton::uint32 getNumberOfPathConstraints(void) const;

          //! Adds a path constraint.
          void addPathConstraint(triton::engines::symbolic::SymbolicExpression* expr);

          //! Clears the logical conjunction vector of path constraints.
          void clearPathConstraints(void);
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PATHMANAGER_H */

