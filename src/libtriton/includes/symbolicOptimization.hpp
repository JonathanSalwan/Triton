//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SYMBOLICOPTIMIZATION_H
#define TRITON_SYMBOLICOPTIMIZATION_H

#include <set>
#include "tritonTypes.hpp"

#ifdef TRITON_PYTHON_BINDINGS
  #ifdef __unix__
    #include <python2.7/Python.h>
  #elif _WIN32
    #include <Python.h>
  #endif
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

      //! Kinds of symbolic optimization.
      enum optimization_e {
        ALIGNED_MEMORY,      //!< Keep a map of aligned memory.
        AST_SUMMARIES,       //!< Abstract Syntax Tree summaries.
        ONLY_ON_TAINTED = 1, //!< Perform symbolic execution only on tainted instructions.
      };

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
          bool isOptimizationEnabled(enum optimization_e opti);

          //! Disables a symbolic optimization.
          void disableOptimization(enum optimization_e opti);

          //! Enables a symbolic optimization.
          void enableOptimization(enum optimization_e opti);
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICSIMPLIFICATION_H */

