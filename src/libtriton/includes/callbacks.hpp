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
      MEMORY_HIT,               /*!< Memory hits callback */
      SYMBOLIC_SIMPLIFICATION,  /*!< Symbolic simplification callback */
    };

    /*! \brief The prototype of a memory hit callback.
     *
     * \description The callback takes as uniq argument an address which representes the memory
     * cell hit. Callbacks will be called each time that a memory cell will be hit.
     */
    typedef void (*memoryHitCallback)(triton::uint64 address);

    /*! \brief The prototype of a symbolic simplification callback.
     *
     * \description The callback takes as uniq argument an triton::ast::AbstractNode and must return a valid triton::ast::AbstractNode.
     * The returned node is used as assignment. See also the page about \ref SMT_simplification_page.
     */
    typedef triton::ast::AbstractNode* (*symbolicSimplificationCallback)(triton::ast::AbstractNode* node);

    //! \class Callbacks
    /*! \brief The callbacks class */
    class Callbacks {
      protected:
        #ifdef TRITON_PYTHON_BINDINGS
        //! [python] Callbacks for all memory hits.
        std::list<PyObject*> pyMemoryHitCallbacks;

        //! [python] Callbacks for all symbolic simplifications.
        std::list<PyObject*> pySymbolicSimplificationCallbacks;
        #endif

        //! [c++] Callbacks for all memory hits.
        std::list<triton::callbacks::memoryHitCallback> memoryHitCallbacks;

        //! [c++] Callbacks for all symbolic simplifications.
        std::list<triton::callbacks::symbolicSimplificationCallback> symbolicSimplificationCallbacks;

        //! Returns the number of callbacks recorded.
        triton::usize countCallbacks(void) const;

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

        //! Adds a memory hit callback.
        void addCallback(triton::callbacks::memoryHitCallback cb);

        //! Adds a symbolic simplification callback.
        void addCallback(triton::callbacks::symbolicSimplificationCallback cb);

        #ifdef TRITON_PYTHON_BINDINGS
        //! Adds a python callback.
        void addCallback(PyObject* function, triton::callbacks::callback_e kind);
        #endif

        //! Deletes a memory hit callback.
        void removeCallback(triton::callbacks::memoryHitCallback cb);

        //! Deletes a symbolic simplification callback.
        void removeCallback(triton::callbacks::symbolicSimplificationCallback cb);

        #ifdef TRITON_PYTHON_BINDINGS
        //! Deletes a python callback.
        void removeCallback(PyObject* function, triton::callbacks::callback_e kind);
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
