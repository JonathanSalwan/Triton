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
   * \description This Helper class is a wrapper around a std::function adding a comparison operator
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
      ComparableFunctor(std::function<Signature> F, void* ID): F_(std::move(F)), ID_(ID) {}

      //! Constructor
      ComparableFunctor(Signature* F): F_(F), ID_((void*)F) {}

      //! Forward call to real functor
      template <class ...T>
      auto operator()(T && ...t) const -> decltype(this->F_(std::forward<T>(t)...)) {
        return F_(std::forward<T>(t)...);
      }

      //! Comparison of functor based on id
      template <class T>
      bool operator==(ComparableFunctor<T> const& O) const {
        return this->ID_ == O.ID_;
      }

      //! Comparison of functor based on id
      template <class T>
      bool operator!=(ComparableFunctor<T> const& O) const {
        return !(this->ID_ == O.ID_);
      }
  };
/*! @} End of triton namespace */
}

#endif
