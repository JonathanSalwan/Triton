//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SOLVERINTERFACE_HPP
#define TRITON_SOLVERINTERFACE_HPP

#include <list>
#include <map>

#include <triton/ast.hpp>
#include <triton/triton_export.h>
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

      /*! \interface SolverInterface
          \brief This interface is used to interface with solvers */
      class SolverInterface {
        public:
          //! Destructor.
          TRITON_EXPORT virtual ~SolverInterface(){};

          //! Computes and returns a model from a symbolic constraint.
          /*! \brief map of symbolic variable id -> model
           *
           * \details
           * **item1**: symbolic variable id<br>
           * **item2**: model
           */
          TRITON_EXPORT virtual std::map<triton::uint32, SolverModel> getModel(const triton::ast::SharedAbstractNode& node) const = 0;

          //! Computes and returns several models from a symbolic constraint. The `limit` is the max number of models returned.
          /*! \brief list of map of symbolic variable id -> model
           *
           * \details
           * **item1**: symbolic variable id<br>
           * **item2**: model
           */
          TRITON_EXPORT virtual std::vector<std::map<triton::uint32, SolverModel>> getModels(const triton::ast::SharedAbstractNode& node, triton::uint32 limit) const = 0;

          //! Returns true if an expression is satisfiable.
          TRITON_EXPORT virtual bool isSat(const triton::ast::SharedAbstractNode& node) const = 0;

          //! Returns the name of the solver.
          TRITON_EXPORT virtual std::string getName(void) const = 0;
      };

    /*! @} End of solver namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SOLVERINTERFACE_HPP */
