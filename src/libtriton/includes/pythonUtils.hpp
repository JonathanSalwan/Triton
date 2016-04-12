//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#ifndef TRITON_PYTHONUTILS_H
#define TRITON PYTHONUTILS_H

#include "pythonBindings.hpp"
#include "tritonTypes.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Bindings namespace
  namespace bindings {
  /*!
   *  \ingroup triton
   *  \addtogroup bindings
   *  @{
   */

    //! \module The Python namespace
    namespace python {
    /*!
     *  \ingroup bindings
     *  \addtogroup python
     *  @{
     */

      //! Returns a triton::__uint from a pyObject.
      triton::__uint PyLong_AsUint(PyObject* obj);

      //! Returns a triton::uint128 from a pyObject.
      triton::uint128 PyLong_AsUint128(PyObject* obj);

      //! Returns a triton::uint256 from a pyObject.
      triton::uint256 PyLong_AsUint256(PyObject* obj);

      //! Returns a triton::uint512 from a pyObject.
      triton::uint512 PyLong_AsUint512(PyObject* obj);

      //! Returns a pyObject from a triton::__uint.
      PyObject* PyLong_FromUint(triton::__uint value);

      //! Returns a pyObject from a triton::uint128.
      PyObject* PyLong_FromUint128(triton::uint128 value);

      //! Returns a pyObject from a triton::uint256.
      PyObject* PyLong_FromUint256(triton::uint256 value);

      //! Returns a pyObject from a triton::uint512.
      PyObject* PyLong_FromUint512(triton::uint512 value);

    /*! @} End of python namespace */
    };
  /*! @} End of bindings namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PYTHONUTILS_H */
#endif /* TRITON_PYTHON_BINDINGS*/
