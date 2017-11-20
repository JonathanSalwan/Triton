//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SOLVERMODEL_H
#define TRITON_SOLVERMODEL_H

#include <tritoncore/types.hpp>

#include <string>


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
    namespace solvers {
      /*!
       *  \ingroup ast
       *  \addtogroup solvers
       *  @{
       */

      //! \class Model
      /*! \brief This class is used to represent a constraint model solved. */
      class Model{
        protected:
          //! The name of the variable. Names are always something like this: SymVar_X.
          std::string name;

          //! The value of the model.
          triton::uint512 value;

        public:
          //! Constructor.
          Model();

          //! Constructor.
          Model(const std::string& name, triton::uint512 value);

          //! Constructor by copy.
          Model(const Model& other);

          //! Copies a Model
          void operator=(const Model& other);

          //! Returns the name of the variable.
          const std::string& getName(void) const;

          //! Returns the value of the model.
          triton::uint512 getValue(void) const;

          //! Copies a Model
          void copy(const Model& other);
      };

      //! Display a solver model.
      std::ostream& operator<<(std::ostream& stream, const Model& model);

      //! Display a solver model.
      std::ostream& operator<<(std::ostream& stream, const Model* model);

      /*! @} End of solvers namespace */
    }
    /*! @} End of ast namespace */
  }
  /*! @} End of triton namespace */
}

#endif /* TRITON_SOLVERMODEL_H */
