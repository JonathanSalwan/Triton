//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITONXPYFUNCTION_H
#define TRITONXPYFUNCTION_H

#include <triton/pythonBindings.hpp>



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

      //! Creates a PyClass and raises an exception if it fails. __dict__ is copied in Py3 ! All references are decremented.
      TRITON_EXPORT PyObject* xPyClass_New(PyObject* b, PyObject* d, PyObject* n);

      //! Creates a PyDict and raises an exception if it fails.
      TRITON_EXPORT PyObject* xPyDict_New(void);

      //! Creates a PyList and raises an exception if it fails.
      TRITON_EXPORT PyObject* xPyList_New(Py_ssize_t len);

      //! Creates a PyString and raises an exception if it fails.
      TRITON_EXPORT PyObject* xPyString_FromString(const char *v);

      //! Creates a PyTuple and raises an exception if it fails.
      TRITON_EXPORT PyObject* xPyTuple_New(Py_ssize_t len);

      //! Same as PyDict_SetItemString but decrements reference on object
      TRITON_EXPORT int xPyDict_SetItemString(PyObject *p, const char *key, PyObject *val);

      //! Same as PyDict_SetItem but decrements reference on object and key
      TRITON_EXPORT int xPyDict_SetItem(PyObject *p, PyObject* key, PyObject *val);

    /*! @} End of python namespace */
    };
  /*! @} End of bindings namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITONXPYFUNCTION_H */
