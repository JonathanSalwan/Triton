//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SOLVERMODEL_H
#define TRITON_SOLVERMODEL_H

#include <string>

#include <triton/triton_export.h>
#include <triton/symbolicVariable.hpp>
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

      //! \class SolverModel
      /*! \brief This class is used to represent a constraint model solved. */
      class SolverModel {
        protected:
          //! The symbolic variable.
          triton::engines::symbolic::SharedSymbolicVariable variable;

          //! The value of the model.
          triton::uint512 value;

        private:
          //! Copies a SolverModel
          void copy(const SolverModel& other);

        public:
          //! Constructor.
          TRITON_EXPORT SolverModel();

          //! Constructor.
          TRITON_EXPORT SolverModel(const triton::engines::symbolic::SharedSymbolicVariable& variable, triton::uint512 value);

          //! Constructor by copy.
          TRITON_EXPORT SolverModel(const SolverModel& other);

          //! Copies a SolverModel
          TRITON_EXPORT SolverModel& operator=(const SolverModel& other);

          //! Returns the id of the variable.
          TRITON_EXPORT triton::usize getId(void) const;

          //! Returns the value of the model.
          TRITON_EXPORT triton::uint512 getValue(void) const;

          //! Returns the symbolic variable.
          TRITON_EXPORT const triton::engines::symbolic::SharedSymbolicVariable& getVariable(void) const;
      };

    //! Display a solver model.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const SolverModel& model);

    //! Display a solver model.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const SolverModel* model);

    /*! @} End of solver namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SOLVERMODEL_H */
