//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_Z3SOLVER_H
#define TRITON_Z3SOLVER_H

#include <list>
#include <map>
#include <string>

#include <triton/ast.hpp>
#include <triton/dllexport.hpp>
#include <triton/solverInterface.hpp>
#include <triton/solverModel.hpp>
#include <triton/symbolicEngine.hpp>
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
    //! The Solver namespace
    namespace solver {
    /*!
     *  \ingroup engines
     *  \addtogroup solver
     *  @{
     */

      //! \class Z3Solver
      /*! \brief Solver engine using z3. */
      class Z3Solver : public SolverInterface {
        private:
          //! Symbolic Engine API
          triton::engines::symbolic::SymbolicEngine* symbolicEngine;

        public:
          //! Constructor.
          TRITON_EXPORT Z3Solver(triton::engines::symbolic::SymbolicEngine* symbolicEngine);

          //! Constructor by copy.
          TRITON_EXPORT Z3Solver(const Z3Solver& other);

          //! Operator.
          TRITON_EXPORT Z3Solver& operator=(const Z3Solver& other);

          //! Computes and returns a model from a symbolic constraint.
          /*! \brief map of symbolic variable id -> model
           *
           * \details
           * **item1**: symbolic variable id<br>
           * **item2**: model
           */
          TRITON_EXPORT std::map<triton::uint32, SolverModel> getModel(const triton::ast::SharedAbstractNode& node) const;

          //! Computes and returns several models from a symbolic constraint. The `limit` is the number of models returned.
          /*! \brief list of map of symbolic variable id -> model
           *
           * \details
           * **item1**: symbolic variable id<br>
           * **item2**: model
           */
          TRITON_EXPORT std::list<std::map<triton::uint32, SolverModel>> getModels(const triton::ast::SharedAbstractNode& node, triton::uint32 limit) const;

          //! Returns true if an expression is satisfiable.
          TRITON_EXPORT bool isSat(const triton::ast::SharedAbstractNode& node) const;

          //! Returns the name of this solver.
          TRITON_EXPORT std::string getName(void) const;
      };

    /*! @} End of solver namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_Z3SOLVER_H */
