//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_BITWUZLASOLVER_H
#define TRITON_BITWUZLASOLVER_H

#include <chrono>
#include <string>
#include <unordered_map>
#include <vector>

extern "C" {
#include <bitwuzla/c/bitwuzla.h>
}

#include <triton/ast.hpp>
#include <triton/dllexport.hpp>
#include <triton/solverEnums.hpp>
#include <triton/solverInterface.hpp>
#include <triton/solverModel.hpp>
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
    //! The Solver namespace
    namespace solver {
    /*!
     *  \ingroup engines
     *  \addtogroup solver
     *  @{
     */

      //! \class BitwuzlaSolver
      /*! \brief Solver engine using Bitwuzla. */
      class BitwuzlaSolver : public SolverInterface {
        private:
          //! Converts binary bitvector value from string to uint512.
          triton::uint512 fromBvalueToUint512(const char* value) const;

          /*! Struct used to provide information for Bitwuzla termination callback */
          struct SolverParams {
            SolverParams(int64_t timeout, size_t memory_limit): timeout(timeout), memory_limit(memory_limit) {
            }

            std::chrono::time_point<std::chrono::system_clock> start = std::chrono::system_clock::now();    /*!< Solver starting time. */
            triton::engines::solver::status_e status = triton::engines::solver::UNKNOWN;                    /*!< Reason of solving termination. */
            int64_t timeout;                                                                                /*!< Timeout (ms) for solver instance running. */
            size_t  memory_limit;                                                                           /*!< Memory limit for the whole symbolic process. */
            int64_t last_mem_check = -1;                                                                    /*!< Time when the last memory usage check was performed. */
          };

          //! The SMT solver timeout. By default, unlimited. This global timeout may be changed for a specific query (isSat/getModel/getModels) via argument `timeout`.
          triton::uint32 timeout;

          //! The SMT solver memory limit. By default, unlimited.
          triton::uint32 memoryLimit;

        public:
          //! Constructor.
          TRITON_EXPORT BitwuzlaSolver();

          //! Computes and returns a model from a symbolic constraint.
          /*! \brief map of symbolic variable id -> model
           *
           * \details
           * **item1**: symbolic variable id<br>
           * **item2**: model
           */
          TRITON_EXPORT std::unordered_map<triton::usize, SolverModel> getModel(const triton::ast::SharedAbstractNode& node, triton::engines::solver::status_e* status = nullptr, triton::uint32 timeout = 0, triton::uint32* solvingTime = nullptr) const;

          //! Computes and returns several models from a symbolic constraint. The `limit` is the number of models returned.
          /*! \brief vector of map of symbolic variable id -> model
           *
           * \details
           * **item1**: symbolic variable id<br>
           * **item2**: model
           */
          TRITON_EXPORT std::vector<std::unordered_map<triton::usize, SolverModel>> getModels(const triton::ast::SharedAbstractNode& node, triton::uint32 limit, triton::engines::solver::status_e* status = nullptr, triton::uint32 timeout = 0, triton::uint32* solvingTime = nullptr) const;

          //! Returns true if an expression is satisfiable.
          TRITON_EXPORT bool isSat(const triton::ast::SharedAbstractNode& node, triton::engines::solver::status_e* status = nullptr, triton::uint32 timeout = 0, triton::uint32* solvingTime = nullptr) const;

          //! Evaluates a Triton's AST via Bitwuzla and returns a concrete value.
          TRITON_EXPORT triton::uint512 evaluate(const triton::ast::SharedAbstractNode& node) const;

          //! Returns the name of this solver.
          TRITON_EXPORT std::string getName(void) const;

          //! Defines a solver timeout (in milliseconds).
          TRITON_EXPORT void setTimeout(triton::uint32 ms);

          //! Defines a solver memory consumption limit (in megabytes).
          TRITON_EXPORT void setMemoryLimit(triton::uint32 mem);

          //! Callback function that implements termination of Bitwuzla solver on timeout and memory limit.
          static int32_t terminateCallback(void* state);

          //! Callback function that implements aborting of Bitwuzla solver with throwing exception.
          static void abortCallback(const char* msg);
      };

    /*! @} End of solver namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_BITWUZLASOLVER_H */
