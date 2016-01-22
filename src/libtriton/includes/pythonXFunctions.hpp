//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef  TRITON_PYTHON_BINDINGS

#ifndef TRITONXPYFUNCTION_H
#define TRITONXPYFUNCTION_H

#ifdef __unix__
  #include <python2.7/Python.h>
#elif _WIN32
  #include <Python.h>
#endif



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

      //! Creates a PyClass and raises an exception if it fails.
      PyObject* xPyClass_New(PyObject* b, PyObject* d, PyObject* n);

      //! Creates a PyDict and raises an exception if it fails.
      PyObject* xPyDict_New(void);

      //! Creates a PyList and raises an exception if it fails.
      PyObject* xPyList_New(Py_ssize_t len);

      //! Creates a PyString and raises an exception if it fails.
      PyObject* xPyString_FromString(const char *v);

      //! Creates a PyTuple and raises an exception if it fails.
      PyObject* xPyTuple_New(Py_ssize_t len);

    /*! @} End of python namespace */
    };
  /*! @} End of bindings namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITONXPYFUNCTION_H */
#endif /* TRITON_PYTHON_BINDINGS */
