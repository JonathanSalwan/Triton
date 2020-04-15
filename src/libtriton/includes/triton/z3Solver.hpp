//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_Z3SOLVER_H
#define TRITON_Z3SOLVER_H

#include <string>
#include <unordered_map>
#include <vector>

#include <triton/ast.hpp>
#include <triton/dllexport.hpp>
#include <triton/solverInterface.hpp>
#include <triton/solverModel.hpp>
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
        public:
          //! Constructor.
          TRITON_EXPORT Z3Solver();

          //! Computes and returns a model from a symbolic constraint.
          /*! \brief map of symbolic variable id -> model
           *
           * \details
           * **item1**: symbolic variable id<br>
           * **item2**: model
           */
          TRITON_EXPORT std::unordered_map<triton::usize, SolverModel> getModel(const triton::ast::SharedAbstractNode& node) const;

          //! Computes and returns several models from a symbolic constraint. The `limit` is the number of models returned.
          /*! \brief vector of map of symbolic variable id -> model
           *
           * \details
           * **item1**: symbolic variable id<br>
           * **item2**: model
           */
          TRITON_EXPORT std::vector<std::unordered_map<triton::usize, SolverModel>> getModels(const triton::ast::SharedAbstractNode& node, triton::uint32 limit) const;

          //! Returns true if an expression is satisfiable.
          TRITON_EXPORT bool isSat(const triton::ast::SharedAbstractNode& node) const;

          //! Converts a Triton's AST to a Z3's AST, perform a Z3 simplification and returns a Triton's AST.
          TRITON_EXPORT triton::ast::SharedAbstractNode simplify(const triton::ast::SharedAbstractNode& node) const;

          //! Evaluates a Triton's AST via Z3 and returns a concrete value.
          TRITON_EXPORT triton::uint512 evaluate(const triton::ast::SharedAbstractNode& node) const;

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
