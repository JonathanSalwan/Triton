//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <stdexcept>
#include <tritonTypes.hpp>
#include <pythonBindings.hpp>
#include <pythonUtils.hpp>

#ifdef __unix__
  #include <python2.7/Python.h>
  #include <python2.7/longintrepr.h>
#elif _WIN32
  #include <Python.h>
#endif



namespace triton {
  namespace bindings {
    namespace python {

      triton::__uint PyLong_AsUint(PyObject* vv) {
        PyLongObject *v;
        triton::__uint x, prev;
        Py_ssize_t i;

        if (vv == NULL || !PyLong_Check(vv)) {
          if (vv != NULL && PyInt_Check(vv)) {
              triton::__uint val = PyInt_AsLong(vv);
              return val;
          }
          throw std::runtime_error("Error: PyLong_AsUint(): Bad internal call");
        }

        v = reinterpret_cast<PyLongObject *>(vv);
        i = Py_SIZE(v);
        x = 0;
        if (i < 0)
          throw std::runtime_error("Error: PyLong_AsUint(): can't convert negative value to unsigned long");

        while (--i >= 0) {
            prev = x;
            x = (x << PyLong_SHIFT) | v->ob_digit[i];
            if ((x >> PyLong_SHIFT) != prev)
                throw std::runtime_error("Error: PyLong_AsUint(): long int too large to convert");
        }

        return x;
      }


      triton::uint128 PyLong_AsUint128(PyObject* vv) {
        PyLongObject *v;
        triton::uint128 x, prev;
        Py_ssize_t i;

        if (vv == NULL || !PyLong_Check(vv)) {
          if (vv != NULL && PyInt_Check(vv)) {
              triton::uint128 val = PyInt_AsLong(vv);
              return val;
          }
          throw std::runtime_error("Error: PyLong_AsUint128(): Bad internal call");
        }

        v = reinterpret_cast<PyLongObject *>(vv);
        i = Py_SIZE(v);
        x = 0;
        if (i < 0)
          throw std::runtime_error("Error: PyLong_AsUint128(): can't convert negative value to unsigned long");

        while (--i >= 0) {
            prev = x;
            x = (x << PyLong_SHIFT) | v->ob_digit[i];
            if ((x >> PyLong_SHIFT) != prev)
                throw std::runtime_error("Error: PyLong_AsUint128(): long int too large to convert");
        }

        return x;
      }


      triton::uint256 PyLong_AsUint256(PyObject* vv) {
        PyLongObject *v;
        triton::uint256 x, prev;
        Py_ssize_t i;

        if (vv == NULL || !PyLong_Check(vv)) {
          if (vv != NULL && PyInt_Check(vv)) {
              triton::uint256 val = PyInt_AsLong(vv);
              return val;
          }
          throw std::runtime_error("Error: PyLong_AsUint256(): Bad internal call");
        }

        v = reinterpret_cast<PyLongObject *>(vv);
        i = Py_SIZE(v);
        x = 0;
        if (i < 0)
          throw std::runtime_error("Error: PyLong_AsUint256(): can't convert negative value to unsigned long");

        while (--i >= 0) {
            prev = x;
            x = (x << PyLong_SHIFT) | v->ob_digit[i];
            if ((x >> PyLong_SHIFT) != prev)
                throw std::runtime_error("Error: PyLong_AsUint256(): long int too large to convert");
        }

        return x;
      }


      triton::uint512 PyLong_AsUint512(PyObject* vv) {
        PyLongObject *v;
        triton::uint512 x, prev;
        Py_ssize_t i;

        if (vv == NULL || !PyLong_Check(vv)) {
          if (vv != NULL && PyInt_Check(vv)) {
              triton::uint512 val = PyInt_AsLong(vv);
              return val;
          }
          throw std::runtime_error("Error: PyLong_AsUint512(): Bad internal call");
        }

        v = reinterpret_cast<PyLongObject *>(vv);
        i = Py_SIZE(v);
        x = 0;
        if (i < 0)
          throw std::runtime_error("Error: PyLong_AsUint512(): can't convert negative value to unsigned long");

        while (--i >= 0) {
            prev = x;
            x = (x << PyLong_SHIFT) | v->ob_digit[i];
            if ((x >> PyLong_SHIFT) != prev)
                throw std::runtime_error("Error: PyLong_AsUint512(): long int too large to convert");
        }

        return x;
      }


      /* Returns a PyObject from a {32,64}-bits integer */
      PyObject* PyLong_FromUint(triton::__uint value) {
        PyLongObject *v;
        triton::__uint t;
        int ndigits = 0;

        /* Count the number of Python digits. */
        t = value;
        while (t) {
          ++ndigits;
          t >>= PyLong_SHIFT;
        }

        v = _PyLong_New(ndigits);
        digit *p = v->ob_digit;
        Py_SIZE(v) = ndigits;
        while (value) {
          *p++ = static_cast<digit>(value & PyLong_MASK);
          value >>= PyLong_SHIFT;
        }

        return (PyObject* )v;
      }


      /* Returns a PyObject from a 128-bits integer */
      PyObject* PyLong_FromUint128(triton::uint128 value) {
        PyLongObject *v;
        triton::uint128 t;
        int ndigits = 0;

        /* Count the number of Python digits. */
        t = value;
        while (t) {
          ++ndigits;
          t >>= PyLong_SHIFT;
        }

        v = _PyLong_New(ndigits);
        digit *p = v->ob_digit;
        Py_SIZE(v) = ndigits;
        while (value) {
          *p++ = static_cast<digit>(value & PyLong_MASK);
          value >>= PyLong_SHIFT;
        }

        return (PyObject* )v;
      }


      /* Returns a PyObject from a 256-bits integer */
      PyObject* PyLong_FromUint256(triton::uint256 value) {
        PyLongObject *v;
        triton::uint256 t;
        int ndigits = 0;

        /* Count the number of Python digits. */
        t = value;
        while (t) {
          ++ndigits;
          t >>= PyLong_SHIFT;
        }

        v = _PyLong_New(ndigits);
        digit *p = v->ob_digit;
        Py_SIZE(v) = ndigits;
        while (value) {
          *p++ = static_cast<digit>(value & PyLong_MASK);
          value >>= PyLong_SHIFT;
        }

        return (PyObject* )v;
      }


      /* Returns a PyObject from a 512-bits integer */
      PyObject* PyLong_FromUint512(triton::uint512 value) {
        PyLongObject *v;
        triton::uint512 t = 0;
        int ndigits = 0;

        /* Count the number of Python digits. */
        t = value;
        while (t) {
          ++ndigits;
          t >>= PyLong_SHIFT;
        }

        v = _PyLong_New(ndigits);
        digit *p = v->ob_digit;
        Py_SIZE(v) = ndigits;
        while (value) {
          *p++ = static_cast<digit>(value & PyLong_MASK);
          value >>= PyLong_SHIFT;
        }

        return (PyObject* )v;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */

