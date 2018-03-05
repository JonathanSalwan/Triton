//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_COMPARABLE_FUNCTOR_H
#define TRITON_COMPARABLE_FUNCTOR_H

#include <functional>
#include <utility>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  /*!
   * \class ComparableFunctor
   * \details This Helper class is a wrapper around a std::function adding a comparison operator
   * to make it searchable in a list even with lambda function.
   */
  template <class Signature>
  struct ComparableFunctor {
    private:
      //! The functor use when called
      std::function<Signature> F_;

      //! Id use for functor comparison
      void* ID_;

    public:
      //! Constructor
      ComparableFunctor(std::function<Signature> F, void* ID)
        : F_(std::move(F)), ID_(ID) {
      }

      //! Constructor
      ComparableFunctor(Signature* F)
        : F_(F), ID_((void*)F) {
      }

      //! Forward call to real functor
      template <class apiType, class paramType>
      auto operator()(apiType& api, paramType& param) const -> decltype(F_(api, param)) {
        return F_(api, param);
      }

      //! Forward call to real functor
      template <class apiType, class paramType1, class paramType2>
      auto operator()(apiType& api, paramType1& param1, paramType2& param2) const -> decltype(F_(api, param1, param2)) {
        /* We don't use C++ variadic templates to support VS2013... */
        return F_(api, param1, param2);
      }

      //! Comparison of functor based on id
      template <class T>
      bool operator==(const ComparableFunctor<T>& O) const {
        return this->ID_ == O.ID_;
      }

      //! Comparison of functor based on id
      template <class T>
      bool operator!=(const ComparableFunctor<T>& O) const {
        return !(this->ID_ == O.ID_);
      }
  };
/*! @} End of triton namespace */
}

#endif
