//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SYMBOLICSIMPLIFICATION_H
#define TRITON_SYMBOLICSIMPLIFICATION_H

#include <list>
#include "tritonTypes.hpp"
#include "smt2lib.hpp"

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

      typedef smt2lib::smtAstAbstractNode* (*sfp)(smt2lib::smtAstAbstractNode*);

      //! \class SymbolicSimplification
      /*! \brief The symbolic simplification class */
      class SymbolicSimplification {

        protected:
          //! List of simplification callbacks. These callbacks will be called before assigning a symbolic expression to a register or part of memory.
          std::list<triton::engines::symbolic::sfp> simplificationCallbacks;

          #ifdef TRITON_PYTHON_BINDINGS
          //! List of simplification callbacks python. These callbacks will be called before assigning a symbolic expression to a register or part of memory.
          std::list<PyObject*> pySimplificationCallbacks;
          #endif

        public:
          //! Constructor.
          SymbolicSimplification();

          //! Destructor.
          ~SymbolicSimplification();

          //! Records a simplification callback.
          void recordSimplificationCallback(triton::engines::symbolic::sfp cb);

          #ifdef TRITON_PYTHON_BINDINGS
          //! Records a simplification callback.
          void recordSimplificationCallback(PyObject* cb);
          #endif

          //! Removes a simplification callback.
          void removeSimplificationCallback(triton::engines::symbolic::sfp cb);

          #ifdef TRITON_PYTHON_BINDINGS
          //! Removes a simplification callback.
          void removeSimplificationCallback(PyObject* cb);
          #endif

          //! Processes all recorded simplifications. Returns the simplified node.
          smt2lib::smtAstAbstractNode* processSimplification(smt2lib::smtAstAbstractNode* node);
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICSIMPLIFICATION_H */

