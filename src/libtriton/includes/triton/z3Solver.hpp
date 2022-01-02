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
#include <z3++.h>
#include <z3_api.h>

#include <triton/ast.hpp>
#include <triton/dllexport.hpp>
#include <triton/solverEnums.hpp>
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
          //! Wrapper to handle variadict number of arguments or'd together.
          static z3::expr mk_or(z3::expr_vector args);

        private:
          //! The SMT solver timeout. By default, unlimited. This global timeout may be changed for a specific query (isSat/getModel/getModels) via argument `timeout`.
          triton::uint32 timeout;

          //! The SMT solver memory limit. By default, unlimited.
          triton::uint32 memoryLimit;

          //! Writes back the status code of the solver into the pointer pointed by status.
          void writeBackStatus(z3::solver& solver, z3::check_result res, triton::engines::solver::status_e* status) const;

        public:
          //! Constructor.
          TRITON_EXPORT Z3Solver();

          //! Computes and returns a model from a symbolic constraint. State is returned in the `status` pointer as well as the solving time. A `timeout` can also be defined.
          /*! \brief map of symbolic variable id -> model
           *
           * \details
           * **item1**: symbolic variable id<br>
           * **item2**: model
           */
          TRITON_EXPORT std::unordered_map<triton::usize, SolverModel> getModel(const triton::ast::SharedAbstractNode& node, triton::engines::solver::status_e* status = nullptr, triton::uint32 timeout = 0, triton::uint32* solvingTime = nullptr) const;

          //! Computes and returns several models from a symbolic constraint. The `limit` is the number of models returned. State is returned in the `status` pointer as well as the solving time. A `timeout` can also be defined.
          /*! \brief vector of map of symbolic variable id -> model
           *
           * \details
           * **item1**: symbolic variable id<br>
           * **item2**: model
           */
          TRITON_EXPORT std::vector<std::unordered_map<triton::usize, SolverModel>> getModels(const triton::ast::SharedAbstractNode& node, triton::uint32 limit, triton::engines::solver::status_e* status = nullptr, triton::uint32 timeout = 0, triton::uint32* solvingTime = nullptr) const;

          //! Returns true if an expression is satisfiable.
          TRITON_EXPORT bool isSat(const triton::ast::SharedAbstractNode& node, triton::engines::solver::status_e* status = nullptr, triton::uint32 timeout = 0, triton::uint32* solvingTime = nullptr) const;

          //! Converts a Triton's AST to a Z3's AST, perform a Z3 simplification and returns a Triton's AST.
          TRITON_EXPORT triton::ast::SharedAbstractNode simplify(const triton::ast::SharedAbstractNode& node) const;

          //! Evaluates a Triton's AST via Z3 and returns a concrete value.
          TRITON_EXPORT triton::uint512 evaluate(const triton::ast::SharedAbstractNode& node) const;

          //! Returns the name of this solver.
          TRITON_EXPORT std::string getName(void) const;

          //! Defines a solver timeout (in milliseconds).
          TRITON_EXPORT void setTimeout(triton::uint32 ms);

          //! Defines a solver memory consumption limit (in megabytes).
          TRITON_EXPORT void setMemoryLimit(triton::uint32 mem);
      };

    /*! @} End of solver namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_Z3SOLVER_H */
