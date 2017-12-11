//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SOLVERMODEL_H
#define TRITON_SOLVERMODEL_H

#include <string>

#include <triton/tritonTypes.hpp>
#include <triton/dllexport.hpp>



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
          //! The name of the variable. Names are always something like this: SymVar_X.
          std::string name;

          //! The id of the variable.
          triton::uint32 id;

          //! The value of the model.
          triton::uint512 value;

        private:
          //! Copies a SolverModel
          void copy(const SolverModel& other);

        public:
          //! Constructor.
          TRITON_EXPORT SolverModel();

          //! Constructor.
          TRITON_EXPORT SolverModel(const std::string& name, triton::uint512 value);

          //! Constructor by copy.
          TRITON_EXPORT SolverModel(const SolverModel& other);

          //! Copies a SolverModel
          TRITON_EXPORT SolverModel& operator=(const SolverModel& other);

          //! Returns the name of the variable.
          TRITON_EXPORT const std::string& getName(void) const;

          //! Returns the id of the variable.
          TRITON_EXPORT triton::uint32 getId(void) const;

          //! Returns the value of the model.
          TRITON_EXPORT triton::uint512 getValue(void) const;
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
