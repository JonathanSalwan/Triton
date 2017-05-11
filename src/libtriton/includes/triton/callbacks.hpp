//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_CALLBACKS_H
#define TRITON_CALLBACKS_H

#include <list>                          // for list
#include <triton/comparableFunctor.hpp>  // for ComparableFunctor
#include <triton/tritonTypes.hpp>        // for usize




//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  class API;

  namespace arch {
    class MemoryAccess;
    class RegisterSpec;
  }

  namespace ast {
    class AbstractNode;
  }

  //! The Callbacks namespace
  namespace callbacks {
  /*!
   *  \ingroup triton
   *  \addtogroup callbacks
   *  @{
   */

    /*! Enumerates all kinds callbacks. */
    enum callback_e {
      GET_CONCRETE_MEMORY_VALUE,    /*!< Get concrete memory value callback */
      GET_CONCRETE_REGISTER_VALUE,  /*!< Get concrete register value callback */
      SYMBOLIC_SIMPLIFICATION,      /*!< Symbolic simplification callback */
    };

    /*! \brief The prototype of a GET_CONCRETE_MEMORY_VALUE callback.
     *
     * \details The callback takes as unique argument a memory access. Callbacks will
     * be called each time that the Triton library will need a concrete memory value.
     */
    using getConcreteMemoryValueCallback = ComparableFunctor<void(triton::API&, triton::arch::MemoryAccess&)>;

    /*! \brief The prototype of a GET_CONCRETE_REGISTER_VALUE callback.
     *
     * \details The callback takes as unique argument a register. Callbacks will be
     * called each time that the Triton library will need a concrete register value.
     */
    using getConcreteRegisterValueCallback = ComparableFunctor<void(triton::API&, triton::arch::RegisterSpec&)>;

    /*! \brief The prototype of a SYMBOLIC_SIMPLIFICATION callback.
     *
     * \details The callback takes as uniq argument a triton::ast::AbstractNode and must return a valid triton::ast::AbstractNode.
     * The returned node is used as assignment. See also the page about \ref SMT_simplification_page for more information.
     */
    using symbolicSimplificationCallback = ComparableFunctor<triton::ast::AbstractNode*(triton::API&, triton::ast::AbstractNode*)>;

    //! \class Callbacks
    /*! \brief The callbacks class */
    class Callbacks {
      protected:

        //! [c++] Callbacks for all concrete memory needs.
        std::list<triton::callbacks::getConcreteMemoryValueCallback> getConcreteMemoryValueCallbacks;

        //! [c++] Callbacks for all concrete register needs.
        std::list<triton::callbacks::getConcreteRegisterValueCallback> getConcreteRegisterValueCallbacks;

        //! [c++] Callbacks for all symbolic simplifications.
        std::list<triton::callbacks::symbolicSimplificationCallback> symbolicSimplificationCallbacks;

        //! Returns the number of callbacks recorded.
        triton::usize countCallbacks(void) const;

      public:
        //! True if there is at least one callback defined.
        bool isDefined;

        //! Constructor.
        Callbacks(triton::API& api);

        //! Destructor.
        virtual ~Callbacks();

        //! Adds a GET_CONCRETE_MEMORY_VALUE callback.
        void addCallback(triton::callbacks::getConcreteMemoryValueCallback cb);

        //! Adds a GET_CONCRETE_REGISTER_VALUE callback.
        void addCallback(triton::callbacks::getConcreteRegisterValueCallback cb);

        //! Adds a SYMBOLIC_SIMPLIFICATION callback.
        void addCallback(triton::callbacks::symbolicSimplificationCallback cb);

        //! Removes all recorded callbacks.
        void removeAllCallbacks(void);

        //! Deletes a GET_CONCRETE_MEMORY_VALUE callback.
        void removeCallback(triton::callbacks::getConcreteMemoryValueCallback cb);

        //! Deletes a GET_CONCRETE_REGISTER_VALUE callback.
        void removeCallback(triton::callbacks::getConcreteRegisterValueCallback cb);

        //! Deletes a SYMBOLIC_SIMPLIFICATION callback.
        void removeCallback(triton::callbacks::symbolicSimplificationCallback cb);

        //! Processes callbacks according to the kind and the C++ polymorphism.
        triton::ast::AbstractNode* processCallbacks(triton::callbacks::callback_e kind, triton::ast::AbstractNode* node) const;

        //! Processes callbacks according to the kind and the C++ polymorphism.
        void processCallbacks(triton::callbacks::callback_e kind, const triton::arch::MemoryAccess& mem) const;

        //! Processes callbacks according to the kind and the C++ polymorphism.
        void processCallbacks(triton::callbacks::callback_e kind, const triton::arch::RegisterSpec& reg) const;

      private:
        //! Reference to the API handling these callbacks
        triton::API& api;
    };

  /*! @} End of callbacks namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_CALLBACKS_H */
