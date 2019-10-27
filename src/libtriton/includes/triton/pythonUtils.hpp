//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PYTHONUTILS_H
#define TRITON PYTHONUTILS_H

#include <triton/triton_export.h>
#include <triton/pythonBindings.hpp>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Bindings namespace
  namespace bindings {
  /*!
   *  \ingroup triton
   *  \addtogroup bindings
   *  @{
   */

    //! The Python namespace
    namespace python {
    /*!
     *  \ingroup bindings
     *  \addtogroup python
     *  @{
     */

      //! Returns a bool from a pyObject.
      TRITON_EXPORT bool PyLong_AsBool(PyObject* obj);

      //! Returns a triton::__uint from a pyObject.
      TRITON_EXPORT triton::__uint PyLong_AsUint(PyObject* obj);

      //! Returns a triton::usize from a pyObject.
      TRITON_EXPORT triton::usize PyLong_AsUsize(PyObject* obj);

      //! Returns a triton::uint32 from a pyObject.
      TRITON_EXPORT triton::uint32 PyLong_AsUint32(PyObject* obj);

      //! Returns a triton::uint64 from a pyObject.
      TRITON_EXPORT triton::uint64 PyLong_AsUint64(PyObject* obj);

      //! Returns a triton::uint128 from a pyObject.
      TRITON_EXPORT triton::uint128 PyLong_AsUint128(PyObject* obj);

      //! Returns a triton::uint256 from a pyObject.
      TRITON_EXPORT triton::uint256 PyLong_AsUint256(PyObject* obj);

      //! Returns a triton::uint512 from a pyObject.
      TRITON_EXPORT triton::uint512 PyLong_AsUint512(PyObject* obj);

      //! Returns a pyObject from a triton::__uint.
      TRITON_EXPORT PyObject* PyLong_FromUint(triton::__uint value);

      //! Returns a pyObject from a triton::usize.
      TRITON_EXPORT PyObject* PyLong_FromUsize(triton::usize value);

      //! Returns a pyObject from a triton::uint32.
      TRITON_EXPORT PyObject* PyLong_FromUint32(triton::uint32 value);

      //! Returns a pyObject from a triton::uint64.
      TRITON_EXPORT PyObject* PyLong_FromUint64(triton::uint64 value);

      //! Returns a pyObject from a triton::uint128.
      TRITON_EXPORT PyObject* PyLong_FromUint128(triton::uint128 value);

      //! Returns a pyObject from a triton::uint256.
      TRITON_EXPORT PyObject* PyLong_FromUint256(triton::uint256 value);

      //! Returns a pyObject from a triton::uint512.
      TRITON_EXPORT PyObject* PyLong_FromUint512(triton::uint512 value);

    /*! @} End of python namespace */
    };
  /*! @} End of bindings namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PYTHONUTILS_H */
