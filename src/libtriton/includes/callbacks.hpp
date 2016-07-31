//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_CALLBACKS_H
#define TRITON_CALLBACKS_H

#include <list>

#include "ast.hpp"
#include "tritonTypes.hpp"

#ifdef TRITON_PYTHON_BINDINGS
  #include "pythonBindings.hpp"
#endif



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Callbacks namespace
  namespace callbacks {
  /*!
   *  \ingroup triton
   *  \addtogroup callbacks
   *  @{
   */

    /*! Enumerates all kinds callbacks. */
    enum callback_e {
      UNMAPPED_MEMORY_HIT,      /*!< Unmapped memory hits callback */
      SYMBOLIC_SIMPLIFICATION,  /*!< Symbolic simplification callback */
    };

    /*! \brief The prototype of a unmapped memory hit callback.
     *
     * \description The `address` argument is the memory address which is read but unmapped.
     * Callbacks will be called before all read of unmapped memory.
     */
    typedef void (*unmappedMemoryHitCallback)(triton::uint64 address);

    /*! \brief The prototype of a symbolic simplification callback.
     *
     * \description Take a node as input and return a new node. Callbacks will be called before all
     * symbolic assignments. It's the returned node which will be assigned.
     */
    typedef triton::ast::AbstractNode* (*symbolicSimplificationCallback)(triton::ast::AbstractNode* node);

    //! \class Callbacks
    /*! \brief The callbacks class */
    class Callbacks {
      protected:
        #ifdef TRITON_PYTHON_BINDINGS
        //! [python] Callbacks for all unmapped memory hits.
        std::list<PyObject*> pyUnmappedMemoryHitCallbacks;

        //! [python] Callbacks for all symbolic simplifications.
        std::list<PyObject*> pySymbolicSimplificationCallbacks;
        #endif

        //! [c++] Callbacks for all unmapped memory hits.
        std::list<triton::callbacks::unmappedMemoryHitCallback> unmappedMemoryHitCallbacks;

        //! [c++] Callbacks for all symbolic simplifications.
        std::list<triton::callbacks::symbolicSimplificationCallback> symbolicSimplificationCallbacks;

        //! Returns the number of callbacks recorded.
        triton::uint32 countCallbacks(void) const;

      public:
        //! True if there is at least one callback defined.
        bool isDefined;

        //! Constructor.
        Callbacks();

        //! Constructor.
        Callbacks(const Callbacks& copy);

        //! Destructor.
        ~Callbacks();

        //! Copies a Callbacks class
        void operator=(const Callbacks& copy);

        //! Adds an unmapped memory hit callback.
        void addCallback(triton::callbacks::unmappedMemoryHitCallback cb);

        //! Adds a symbolic simplification callback.
        void addCallback(triton::callbacks::symbolicSimplificationCallback cb);

        #ifdef TRITON_PYTHON_BINDINGS
        //! Adds a python callback.
        void addCallback(triton::callbacks::callback_e kind, PyObject* function);
        #endif

        //! Deletes an unmapped memory hit callback.
        void deleteCallback(triton::callbacks::unmappedMemoryHitCallback cb);

        //! Deletes a symbolic simplification callback.
        void deleteCallback(triton::callbacks::symbolicSimplificationCallback cb);

        #ifdef TRITON_PYTHON_BINDINGS
        //! Deletes a python callback.
        void deleteCallback(triton::callbacks::callback_e kind, PyObject* function);
        #endif

        //! Processes callbacks according to the kind and the C++ polymorphism.
        triton::ast::AbstractNode* processCallbacks(triton::callbacks::callback_e kind, triton::ast::AbstractNode* node) const;

        //! Processes callbacks according to the kind and the C++ polymorphism.
        void processCallbacks(triton::callbacks::callback_e kind, triton::uint64 address) const;
    };

  /*! @} End of callbacks namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_CALLBACKS_H */
