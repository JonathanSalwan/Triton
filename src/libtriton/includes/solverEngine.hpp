//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SOLVERENGINE_H
#define TRITON_SOLVERENGINE_H

#include <cstdlib>
#include <list>
#include <map>
#include <string>

#include <z3++.h>

#include "smt2lib.hpp"
#include "solverModel.hpp"
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
    //! \module The Solver namespace
    namespace solver {
    /*!
     *  \ingroup engines
     *  \addtogroup solver
     *  @{
     */

      //! \class SolverEngine
      /*! \brief The solver engine class. */
      class SolverEngine
      {
        public:
          //! Computes and returns a model from a symbolic constraint.
          /*! \brief map of symbolic variable id -> model
           *
           * \description
           * **item1**: symbolic variable id<br>
           * **item2**: model
           */
          std::map<triton::uint32, SolverModel> getModel(smt2lib::smtAstAbstractNode *node);

          //! Computes and returns several models from a symbolic constraint. The `limit` is the number of models returned.
          /*! \brief list of map of symbolic variable id -> model
           *
           * \description
           * **item1**: symbolic variable id<br>
           * **item2**: model
           */
          std::list<std::map<triton::uint32, SolverModel>> getModels(smt2lib::smtAstAbstractNode *node, triton::uint32 limit);

          //! Evaluates an AST and returns the symbolic value.
          triton::uint512 evaluateAst(smt2lib::smtAstAbstractNode *node);

          //! Constructor.
          SolverEngine();

          //! Destructor.
          ~SolverEngine();
      };

    /*! @} End of solver namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SOLVERENGINE_H */
