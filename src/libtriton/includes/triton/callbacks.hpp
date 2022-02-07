//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_CALLBACKS_H
#define TRITON_CALLBACKS_H

#include <atomic>
#include <list>

#include <triton/ast.hpp>
#include <triton/callbacksEnums.hpp>
#include <triton/comparableFunctor.hpp>
#include <triton/dllexport.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/register.hpp>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  class API;

  //! The Callbacks namespace
  namespace callbacks {
  /*!
   *  \ingroup triton
   *  \addtogroup callbacks
   *  @{
   */

    /*! \brief The prototype of a GET_CONCRETE_MEMORY_VALUE callback.
     *
     * \details The callback takes an API context as first argument and a memory access as second argument.
     * Callbacks will be called each time that the Triton library will need to LOAD a concrete memory value.
     */
    using getConcreteMemoryValueCallback = ComparableFunctor<void(triton::API&, const triton::arch::MemoryAccess&)>;

    /*! \brief The prototype of a GET_CONCRETE_REGISTER_VALUE callback.
     *
     * \details The callback takes an API context as first argument and a register as second argument.
     * Callbacks will be called each time that the Triton library will need to GET a concrete register value.
     */
    using getConcreteRegisterValueCallback = ComparableFunctor<void(triton::API&, const triton::arch::Register&)>;

    /*! \brief The prototype of a SET_CONCRETE_MEMORY_VALUE callback.
     *
     * \details The callback takes an API context as first argument, a memory access as second argument and the value at third.
     * Callbacks will be called each time that the Triton library will need to STORE a concrete memory value.
     */
    using setConcreteMemoryValueCallback = ComparableFunctor<void(triton::API&, const triton::arch::MemoryAccess&, const triton::uint512& value)>;

    /*! \brief The prototype of a SET_CONCRETE_REGISTER_VALUE callback.
     *
     * \details The callback takes an API context as first argument, a register as second argument and the value at third.
     * Callbacks will be called each time that the Triton library will neet to PUT a concrete register value.
     */
    using setConcreteRegisterValueCallback = ComparableFunctor<void(triton::API&, const triton::arch::Register&, const triton::uint512& value)>;

    /*! \brief The prototype of a SYMBOLIC_SIMPLIFICATION callback.
     *
     * \details The callback takes as arguments an API context as first argument and an abstract node as second argument
     * The callback must return a valid abstract node which will be used as assignment according to the instruction semantics.
     * See also the page about \ref SMT_simplification_page for more information about semantic transformations.
     */
    using symbolicSimplificationCallback = ComparableFunctor<triton::ast::SharedAbstractNode(triton::API&, const triton::ast::SharedAbstractNode&)>;

    //! \class Callbacks
    /*! \brief The callbacks class */
    class Callbacks {
      private:
        //! Reference to the API handling these callbacks
        triton::API& api;

        //! Mutex for the getConcreteRegisterValue callback
        std::atomic<bool> mget;

        //! Mutex for the getConcreteMemoryValue callback
        std::atomic<bool> mload;

        //! Mutex for the setConcreteRegisterValue callback
        std::atomic<bool> mput;

        //! Mutex for the setConcreteMemoryValue callback
        std::atomic<bool> mstore;

        //! True if there is at least one callback defined.
        std::atomic<bool> defined;

      protected:
        //! [c++] Callbacks for all concrete memory needs (LOAD).
        std::list<triton::callbacks::getConcreteMemoryValueCallback> getConcreteMemoryValueCallbacks;

        //! [c++] Callbacks for all concrete register needs (GET).
        std::list<triton::callbacks::getConcreteRegisterValueCallback> getConcreteRegisterValueCallbacks;

        //! [c++] Callbacks for all concrete memory needs (STORE).
        std::list<triton::callbacks::setConcreteMemoryValueCallback> setConcreteMemoryValueCallbacks;

        //! [c++] Callbacks for all concrete register needs (PUT).
        std::list<triton::callbacks::setConcreteRegisterValueCallback> setConcreteRegisterValueCallbacks;

        //! [c++] Callbacks for all symbolic simplifications.
        std::list<triton::callbacks::symbolicSimplificationCallback> symbolicSimplificationCallbacks;

        //! Returns the number of callbacks recorded.
        triton::usize countCallbacks(void) const;

        //! Trys to find and remove the callback, raises an exception if not able
        template <typename T> void removeSingleCallback(std::list<T>& container, T cb);

      public:
        //! Constructor.
        TRITON_EXPORT Callbacks(triton::API& api);

        //! Adds a GET_CONCRETE_MEMORY_VALUE callback.
        TRITON_EXPORT void addCallback(triton::callbacks::callback_e kind, ComparableFunctor<void(triton::API&, const triton::arch::MemoryAccess&)> cb);

        //! Adds a GET_CONCRETE_REGISTER_VALUE callback.
        TRITON_EXPORT void addCallback(triton::callbacks::callback_e kind, ComparableFunctor<void(triton::API&, const triton::arch::Register&)> cb);

        //! Adds a SET_CONCRETE_MEMORY_VALUE callback.
        TRITON_EXPORT void addCallback(triton::callbacks::callback_e kind, ComparableFunctor<void(triton::API&, const triton::arch::MemoryAccess&, const triton::uint512& value)> cb);

        //! Adds a SET_CONCRETE_REGISTER_VALUE callback.
        TRITON_EXPORT void addCallback(triton::callbacks::callback_e kind, ComparableFunctor<void(triton::API&, const triton::arch::Register&, const triton::uint512& value)> cb);

        //! Adds a SYMBOLIC_SIMPLIFICATION callback.
        TRITON_EXPORT void addCallback(triton::callbacks::callback_e kind, ComparableFunctor<triton::ast::SharedAbstractNode(triton::API&, const triton::ast::SharedAbstractNode&)> cb);

        //! Clears recorded callbacks.
        TRITON_EXPORT void clearCallbacks(void);

        //! Deletes a GET_CONCRETE_MEMORY_VALUE callback.
        TRITON_EXPORT void removeCallback(triton::callbacks::callback_e kind, ComparableFunctor<void(triton::API&, const triton::arch::MemoryAccess&)> cb);

        //! Deletes a GET_CONCRETE_REGISTER_VALUE callback.
        TRITON_EXPORT void removeCallback(triton::callbacks::callback_e kind, ComparableFunctor<void(triton::API&, const triton::arch::Register&)> cb);

        //! Deletes a SET_CONCRETE_MEMORY_VALUE callback.
        TRITON_EXPORT void removeCallback(triton::callbacks::callback_e kind, ComparableFunctor<void(triton::API&, const triton::arch::MemoryAccess&, const triton::uint512& value)> cb);

        //! Deletes a SET_CONCRETE_REGISTER_VALUE callback.
        TRITON_EXPORT void removeCallback(triton::callbacks::callback_e kind, ComparableFunctor<void(triton::API&, const triton::arch::Register&, const triton::uint512& value)> cb);

        //! Deletes a SYMBOLIC_SIMPLIFICATION callback.
        TRITON_EXPORT void removeCallback(triton::callbacks::callback_e kind, ComparableFunctor<triton::ast::SharedAbstractNode(triton::API&, const triton::ast::SharedAbstractNode&)> cb);

        //! Processes callbacks according to the kind and the C++ polymorphism.
        TRITON_EXPORT triton::ast::SharedAbstractNode processCallbacks(triton::callbacks::callback_e kind, triton::ast::SharedAbstractNode node);

        //! Processes callbacks according to the kind and the C++ polymorphism.
        TRITON_EXPORT void processCallbacks(triton::callbacks::callback_e kind, const triton::arch::MemoryAccess& mem);

        //! Processes callbacks according to the kind and the C++ polymorphism.
        TRITON_EXPORT void processCallbacks(triton::callbacks::callback_e kind, const triton::arch::MemoryAccess& mem, const triton::uint512& value);

        //! Processes callbacks according to the kind and the C++ polymorphism.
        TRITON_EXPORT void processCallbacks(triton::callbacks::callback_e kind, const triton::arch::Register& reg);

        //! Processes callbacks according to the kind and the C++ polymorphism.
        TRITON_EXPORT void processCallbacks(triton::callbacks::callback_e kind, const triton::arch::Register& reg, const triton::uint512& value);

        //! Returns true if the callback is defined.
        TRITON_EXPORT bool isDefined(triton::callbacks::callback_e kind) const;

        //! Returns true if at least one callback is defined.
        TRITON_EXPORT bool isDefined(void) const;
    };

  /*! @} End of callbacks namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_CALLBACKS_H */
