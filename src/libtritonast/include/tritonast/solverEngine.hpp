//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SOLVERENGINE_H
#define TRITON_SOLVERENGINE_H

#include <cstdlib>
#include <list>
#include <map>
#include <string>

#include <z3++.h>

#include <tritonast/nodes.hpp>
#include <tritonast/solver/model.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */
  //! The ast namespace
  namespace ast {
  /*!
   *  \ingroup triton
   *  \addtogroup ast
   *  @{
   */

    /*! 
     * \ingroup ast
     * \addtogroup solver
     * @{
     */
    namespace solver {

      /*! 
       * \ingroup solver
       * \addtogroup z3
       * @{
       */
      namespace z3{

        //! Computes and returns a model from a symbolic constraint.
        /*! \brief map of symbolic variable id -> model
         *
         * \details
         * **item1**: symbolic variable id<br>
         * **item2**: model
         */
        std::map<std::string, SolverModel> getModel(triton::ast::AbstractNode* node);

        //! Computes and returns several models from a symbolic constraint. The `limit` is the number of models returned.
        /*! \brief list of map of symbolic variable id -> model
         *
         * \details
         * **item1**: symbolic variable id<br>
         * **item2**: model
         */
        std::list<std::map<std::string, SolverModel>> getModels(triton::ast::AbstractNode* node, triton::uint32 limit);
        /*! @} End of z3 namespace */
    };
    /*! @} End of solver namespace */
  };
  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SOLVERENGINE_H */
