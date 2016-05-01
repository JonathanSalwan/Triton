//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SYMBOLICOPTIMIZATION_H
#define TRITON_SYMBOLICOPTIMIZATION_H

#include <set>

#include "symbolicEnums.hpp"
#include "tritonTypes.hpp"

#ifdef TRITON_PYTHON_BINDINGS
  #include "pythonBindings.hpp"
#endif



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

    //! \module The Symbolic Execution namespace
    namespace symbolic {
    /*!
     *  \ingroup engines
     *  \addtogroup symbolic
     *  @{
     */

      //! \class SymbolicOptimization
      /*! \brief The symbolic simplification class */
      class SymbolicOptimization {

        protected:
          //! The set of enabled optimization
          std::set<enum optimization_e> enabledOptimizations;

        public:
          //! Constructor.
          SymbolicOptimization();

          //! Destructor.
          ~SymbolicOptimization();

          //! Returns true if the symbolic optimization is enabled.
          bool isOptimizationEnabled(enum optimization_e opti) const;

          //! Enables or disables a symbolic optimization.
          void enableOptimization(enum optimization_e opti, bool flag);
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICSIMPLIFICATION_H */

