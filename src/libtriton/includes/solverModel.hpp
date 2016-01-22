//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SOLVERMODEL_H
#define TRITON_SOLVERMODEL_H

#include <string>
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

      //! \class SolverModel
      /*! \brief This class is used to represent a constraint model solved. */
      class SolverModel
      {
        protected:
          //! The variable's name.
          std::string name;

          //! The variable's id.
          triton::uint32 id;

          //! The model's value.
          triton::uint512 value;

        public:
          //! Returns the variable's name.
          std::string getName(void);

          //! Returns the variable's id.
          triton::uint32 getId(void);

          //! Returns the model's value.
          triton::uint512 getValue(void);

          //! Copies a SolverModel
          void copy(const SolverModel& other);

          //! Constructor.
          SolverModel();

          //! Constructor.
          SolverModel(std::string name, triton::uint512 value);

          //! Constructor by copy.
          SolverModel(const SolverModel& other);

          //! Destructor.
          ~SolverModel();

          //! Copies a SolverModel
          void operator=(const SolverModel& other);
      };

    //! Display a solver model.
    std::ostream &operator<<(std::ostream &stream, SolverModel model);

    /*! @} End of solver namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SOLVERMODEL_H */
