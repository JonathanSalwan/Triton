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
      class SolverModel
      {
        protected:
          //! The name of the variable. Names are always something like this: SymVar_X.
          std::string name;

          //! The id of the variable.
          triton::uint32 id;

          //! The value of the model.
          triton::uint512 value;

        public:
          //! Returns the name of the variable.
          const std::string& getName(void) const;

          //! Returns the id of the variable.
          triton::uint32 getId(void) const;

          //! Returns the value of the model.
          triton::uint512 getValue(void) const;

          //! Copies a SolverModel
          void copy(const SolverModel& other);

          //! Constructor.
          SolverModel();

          //! Constructor.
          SolverModel(const std::string& name, triton::uint512 value);

          //! Constructor by copy.
          SolverModel(const SolverModel& other);

          //! Destructor.
          virtual ~SolverModel();

          //! Copies a SolverModel
          void operator=(const SolverModel& other);
      };

    //! Display a solver model.
    std::ostream& operator<<(std::ostream& stream, const SolverModel& model);

    //! Display a solver model.
    std::ostream& operator<<(std::ostream& stream, const SolverModel* model);

    /*! @} End of solver namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SOLVERMODEL_H */
