//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SOLVERENGINE_HPP
#define TRITON_SOLVERENGINE_HPP

#include <iostream>
#include <list>
#include <map>
#include <memory>

#include <triton/ast.hpp>
#include <triton/triton_export.h>
#include <triton/solverEnums.hpp>
#include <triton/solverInterface.hpp>
#include <triton/solverModel.hpp>
#include <triton/tritonTypes.hpp>
#ifdef Z3_INTERFACE
  #include <triton/z3Solver.hpp>
#endif



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
    //! The Solver namespace
    namespace solver {
    /*!
     *  \ingroup engines
     *  \addtogroup solver
     *  @{
     */

      /*! \interface SolverEngine
          \brief This class is used to interface with solvers */
      class SolverEngine {
        protected:
          //! The kind of the current solver used.
          triton::engines::solver::solver_e kind;

          //! Instance to the real solver class.
          std::unique_ptr<triton::engines::solver::SolverInterface> solver;

        public:
          //! Constructor.
          TRITON_EXPORT SolverEngine();

          //! Returns the kind of solver as triton::engines::solver::solver_e.
          TRITON_EXPORT triton::engines::solver::solver_e getSolver(void) const;

          //! Returns the instance of the initialized solver
          TRITON_EXPORT const triton::engines::solver::SolverInterface* getSolverInstance(void) const;

          //! Initializes a predefined solver.
          TRITON_EXPORT void setSolver(triton::engines::solver::solver_e kind);

          //! Initializes a custom solver.
          TRITON_EXPORT void setCustomSolver(triton::engines::solver::SolverInterface* customSolver);

          //! Returns true if the solver is valid.
          TRITON_EXPORT bool isValid(void) const;

          //! Computes and returns a model from a symbolic constraint.
          /*! \brief map of symbolic variable id -> model
           *
           * \details
           * **item1**: symbolic variable id<br>
           * **item2**: model
           */
          TRITON_EXPORT std::map<triton::uint32, SolverModel> getModel(const triton::ast::SharedAbstractNode& node) const;

          //! Computes and returns several models from a symbolic constraint. The `limit` is the max number of models returned.
          /*! \brief list of map of symbolic variable id -> model
           *
           * \details
           * **item1**: symbolic variable id<br>
           * **item2**: model
           */
          TRITON_EXPORT std::vector<std::map<triton::uint32, SolverModel>> getModels(const triton::ast::SharedAbstractNode& node, triton::uint32 limit) const;

          //! Returns true if an expression is satisfiable.
          TRITON_EXPORT bool isSat(const triton::ast::SharedAbstractNode& node) const;

          //! Returns the name of the solver.
          TRITON_EXPORT std::string getName(void) const;
      };

    /*! @} End of solver namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SOLVERINTERFACE_HPP */
