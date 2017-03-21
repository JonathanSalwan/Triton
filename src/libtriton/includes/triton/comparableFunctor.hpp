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
   * \struct ComparableFunctor
   * \brief This Helper class is a wrapper around a std::function adding a comparison operator to make it searchable in a list even with lambda function.
   */
  template <class Signature>
  struct ComparableFunctor {
    private:
      std::function<Signature> F_;
      void* ID_;

    public:
      ComparableFunctor(std::function<Signature> F, void* ID): F_(std::move(F)), ID_(ID) {}
      ComparableFunctor(Signature* F): F_(F), ID_((void*)F) {}

      template <class ...T>
      auto operator()(T && ...t) const -> decltype(this->F_(std::forward<T>(t)...)) {
        return F_(std::forward<T>(t)...);
      }

      template <class T>
      bool operator==(ComparableFunctor<T> const& O) const {
        return this->ID_ == O.ID_;
      }

      template <class T>
      bool operator!=(ComparableFunctor<T> const& O) const {
        return !(this->ID_ == O.ID_);
      }
  };
/*! @} End of triton namespace */
};

#endif
