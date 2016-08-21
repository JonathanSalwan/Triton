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
#include "register.hpp"
#include "memoryAccess.hpp"
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
      MEMORY_LOAD,              /*!< Memory load callback */
      REGISTER_GET,             /*!< Register get callback */
      SYMBOLIC_SIMPLIFICATION,  /*!< Symbolic simplification callback */
    };

    /*! \brief The prototype of a memory load callback.
     *
     * \description The callback takes as arguments an address which representes the memory
     * cell loaded and his size. Callbacks will be called each time that a memory cell will
     * be loaded.
     */
    typedef void (*memoryLoadCallback)(triton::uint64 address, triton::uint32 size);

    /*! \brief The prototype of a register GET callback.
     *
     * \description The callback takes as unique argument a triton::arch::Register which represents
     * the register which will be read (GET). Callbacks will be called each time that a concrete register
     * will be read.
     */
    typedef void (*registerGetCallback)(const triton::arch::Register& reg);

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
        //! [python] Callbacks for all memory LOADS.
        std::list<PyObject*> pyMemoryLoadCallbacks;

        //! [python] Callbacks for all register GETS.
        std::list<PyObject*> pyRegisterGetCallbacks;

        //! [python] Callbacks for all symbolic simplifications.
        std::list<PyObject*> pySymbolicSimplificationCallbacks;
        #endif

        //! [c++] Callbacks for all memory LOADS.
        std::list<triton::callbacks::memoryLoadCallback> memoryLoadCallbacks;

        //! [c++] Callbacks for all register GETS.
        std::list<triton::callbacks::registerGetCallback> registerGetCallbacks;

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

        //! Adds a memory LOAD callback.
        void addCallback(triton::callbacks::memoryLoadCallback cb);

        //! Adds a register GET callback.
        void addCallback(triton::callbacks::registerGetCallback cb);

        //! Adds a symbolic simplification callback.
        void addCallback(triton::callbacks::symbolicSimplificationCallback cb);

        #ifdef TRITON_PYTHON_BINDINGS
        //! Adds a python callback.
        void addCallback(PyObject* function, triton::callbacks::callback_e kind);
        #endif

        //! Deletes a memory LOAD callback.
        void removeCallback(triton::callbacks::memoryLoadCallback cb);

        //! Deletes a register GET callback.
        void removeCallback(triton::callbacks::registerGetCallback cb);

        //! Deletes a symbolic simplification callback.
        void removeCallback(triton::callbacks::symbolicSimplificationCallback cb);

        #ifdef TRITON_PYTHON_BINDINGS
        //! Deletes a python callback.
        void removeCallback(PyObject* function, triton::callbacks::callback_e kind);
        #endif

        //! Processes callbacks according to the kind and the C++ polymorphism.
        triton::ast::AbstractNode* processCallbacks(triton::callbacks::callback_e kind, triton::ast::AbstractNode* node) const;

        //! Processes callbacks according to the kind and the C++ polymorphism.
        void processCallbacks(triton::callbacks::callback_e kind, const triton::arch::MemoryAccess& mem) const;

        //! Processes callbacks according to the kind and the C++ polymorphism.
        void processCallbacks(triton::callbacks::callback_e kind, const triton::arch::Register& reg) const;
    };

  /*! @} End of callbacks namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_CALLBACKS_H */
