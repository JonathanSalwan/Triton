//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/tritonTypes.hpp>



namespace triton {
  namespace bindings {
    namespace python {

      bool PyLong_AsBool(PyObject* obj) {
        return (PyObject_IsTrue(obj) != 0);
      }


      triton::__uint PyLong_AsUint(PyObject* vv) {
        PyLongObject* v;
        triton::__uint x, prev;
        Py_ssize_t i;

        if (vv == NULL || !PyLong_Check(vv)) {
          if (vv != NULL && PyInt_Check(vv)) {
              triton::__uint val = PyInt_AsLong(vv);
              return val;
          }
          throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint(): Bad internal call.");
        }

        v = reinterpret_cast<PyLongObject*>(vv);
        i = Py_SIZE(v);
        x = 0;
        if (i < 0)
          throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint(): Cannot convert negative value to unsigned long.");

        while (--i >= 0) {
            prev = x;
            x = (x << PyLong_SHIFT) | v->ob_digit[i];
            if ((x >> PyLong_SHIFT) != prev)
                throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint(): long int too large to convert.");
        }

        return x;
      }


      triton::usize PyLong_AsUsize(PyObject* vv) {
        PyLongObject* v;
        triton::usize x, prev;
        Py_ssize_t i;

        if (vv == NULL || !PyLong_Check(vv)) {
          if (vv != NULL && PyInt_Check(vv)) {
              triton::usize val = PyInt_AsLong(vv);
              return val;
          }
          throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUsize(): Bad internal call.");
        }

        v = reinterpret_cast<PyLongObject*>(vv);
        i = Py_SIZE(v);
        x = 0;
        if (i < 0)
          throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUsize(): Cannot convert negative value to unsigned long.");

        while (--i >= 0) {
            prev = x;
            x = (x << PyLong_SHIFT) | v->ob_digit[i];
            if ((x >> PyLong_SHIFT) != prev)
                throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUsize(): long int too large to convert.");
        }

        return x;
      }


      triton::uint32 PyLong_AsUint32(PyObject* vv) {
        PyLongObject* v;
        triton::uint32 x, prev;
        Py_ssize_t i;

        if (vv == NULL || !PyLong_Check(vv)) {
          if (vv != NULL && PyInt_Check(vv)) {
              triton::uint32 val = PyInt_AsLong(vv);
              return val;
          }
          throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint32(): Bad internal call.");
        }

        v = reinterpret_cast<PyLongObject*>(vv);
        i = Py_SIZE(v);
        x = 0;
        if (i < 0)
          throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint32(): Cannot convert negative value to unsigned long.");

        while (--i >= 0) {
            prev = x;
            x = (x << PyLong_SHIFT) | v->ob_digit[i];
            if ((x >> PyLong_SHIFT) != prev)
                throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint32(): long int too large to convert.");
        }

        return x;
      }


      triton::uint64 PyLong_AsUint64(PyObject* vv) {
        PyLongObject* v;
        triton::uint64 x, prev;
        Py_ssize_t i;

        if (vv == NULL || !PyLong_Check(vv)) {
          if (vv != NULL && PyInt_Check(vv)) {
              triton::uint64 val = PyInt_AsLong(vv);
              return val;
          }
          throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint64(): Bad internal call.");
        }

        v = reinterpret_cast<PyLongObject*>(vv);
        i = Py_SIZE(v);
        x = 0;
        if (i < 0)
          throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint64(): Cannot convert negative value to unsigned long.");

        while (--i >= 0) {
            prev = x;
            x = (x << PyLong_SHIFT) | v->ob_digit[i];
            if ((x >> PyLong_SHIFT) != prev)
                throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint64(): long int too large to convert.");
        }

        return x;
      }


      triton::uint128 PyLong_AsUint128(PyObject* vv) {
        PyLongObject* v;
        triton::uint128 x, prev;
        Py_ssize_t i;

        if (vv == NULL || !PyLong_Check(vv)) {
          if (vv != NULL && PyInt_Check(vv)) {
              triton::uint128 val = PyInt_AsLong(vv);
              return val;
          }
          throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint128(): Bad internal call.");
        }

        v = reinterpret_cast<PyLongObject*>(vv);
        i = Py_SIZE(v);
        x = 0;
        if (i < 0)
          throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint128(): Cannot convert negative value to unsigned long.");

        while (--i >= 0) {
            prev = x;
            x = (x << PyLong_SHIFT) | v->ob_digit[i];
            if ((x >> PyLong_SHIFT) != prev)
                throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint128(): long int too large to convert.");
        }

        return x;
      }


      triton::uint256 PyLong_AsUint256(PyObject* vv) {
        PyLongObject* v;
        triton::uint256 x, prev;
        Py_ssize_t i;

        if (vv == NULL || !PyLong_Check(vv)) {
          if (vv != NULL && PyInt_Check(vv)) {
              triton::uint256 val = PyInt_AsLong(vv);
              return val;
          }
          throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint256(): Bad internal call.");
        }

        v = reinterpret_cast<PyLongObject*>(vv);
        i = Py_SIZE(v);
        x = 0;
        if (i < 0)
          throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint256(): Cannot convert negative value to unsigned long.");

        while (--i >= 0) {
            prev = x;
            x = (x << PyLong_SHIFT) | v->ob_digit[i];
            if ((x >> PyLong_SHIFT) != prev)
                throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint256(): long int too large to convert.");
        }

        return x;
      }


      triton::uint512 PyLong_AsUint512(PyObject* vv) {
        PyLongObject* v;
        triton::uint512 x, prev;
        Py_ssize_t i;

        if (vv == NULL || !PyLong_Check(vv)) {
          if (vv != NULL && PyInt_Check(vv)) {
              triton::uint512 val = PyInt_AsLong(vv);
              return val;
          }
          throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint512(): Bad internal call.");
        }

        v = reinterpret_cast<PyLongObject*>(vv);
        i = Py_SIZE(v);
        x = 0;
        if (i < 0)
          throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint512(): Cannot convert negative value to unsigned long.");

        while (--i >= 0) {
            prev = x;
            x = (x << PyLong_SHIFT) | v->ob_digit[i];
            if ((x >> PyLong_SHIFT) != prev)
                throw triton::exceptions::Bindings("triton::bindings::python::PyLong_AsUint512(): long int too large to convert.");
        }

        return x;
      }


      /* Returns a PyObject from a {32,64}-bits integer */
      PyObject* PyLong_FromUint(triton::__uint value) {
        PyLongObject* v;
        triton::__uint t;
        int ndigits = 0;

        /* Count the number of Python digits. */
        t = value;
        while (t) {
          ++ndigits;
          t >>= PyLong_SHIFT;
        }

        v = _PyLong_New(ndigits);
        digit* p = v->ob_digit;
        Py_SIZE(v) = ndigits;
        while (value) {
          *p++ = static_cast<digit>(value & PyLong_MASK);
          value >>= PyLong_SHIFT;
        }

        return (PyObject*)v;
      }


      /* Returns a PyObject from a {32,64}-bits integer */
      PyObject* PyLong_FromUsize(triton::usize value) {
        PyLongObject* v;
        triton::usize t;
        int ndigits = 0;

        /* Count the number of Python digits. */
        t = value;
        while (t) {
          ++ndigits;
          t >>= PyLong_SHIFT;
        }

        v = _PyLong_New(ndigits);
        digit* p = v->ob_digit;
        Py_SIZE(v) = ndigits;
        while (value) {
          *p++ = static_cast<digit>(value & PyLong_MASK);
          value >>= PyLong_SHIFT;
        }

        return (PyObject*)v;
      }


      /* Returns a PyObject from a 32-bits integer */
      PyObject* PyLong_FromUint32(triton::uint32 value) {
        PyLongObject* v;
        triton::uint32 t;
        int ndigits = 0;

        /* Count the number of Python digits. */
        t = value;
        while (t) {
          ++ndigits;
          t >>= PyLong_SHIFT;
        }

        v = _PyLong_New(ndigits);
        digit* p = v->ob_digit;
        Py_SIZE(v) = ndigits;
        while (value) {
          *p++ = static_cast<digit>(value & PyLong_MASK);
          value >>= PyLong_SHIFT;
        }

        return (PyObject*)v;
      }


      /* Returns a PyObject from a 64-bits integer */
      PyObject* PyLong_FromUint64(triton::uint64 value) {
        PyLongObject* v;
        triton::uint64 t;
        int ndigits = 0;

        /* Count the number of Python digits. */
        t = value;
        while (t) {
          ++ndigits;
          t >>= PyLong_SHIFT;
        }

        v = _PyLong_New(ndigits);
        digit* p = v->ob_digit;
        Py_SIZE(v) = ndigits;
        while (value) {
          *p++ = static_cast<digit>(value & PyLong_MASK);
          value >>= PyLong_SHIFT;
        }

        return (PyObject*)v;
      }


      /* Returns a PyObject from a 128-bits integer */
      PyObject* PyLong_FromUint128(triton::uint128 value) {
        PyLongObject* v;
        triton::uint128 t;
        int ndigits = 0;

        /* Count the number of Python digits. */
        t = value;
        while (t) {
          ++ndigits;
          t >>= PyLong_SHIFT;
        }

        v = _PyLong_New(ndigits);
        digit* p = v->ob_digit;
        Py_SIZE(v) = ndigits;
        while (value) {
          *p++ = (value & PyLong_MASK).convert_to<digit>();
          value >>= PyLong_SHIFT;
        }

        return (PyObject*)v;
      }


      /* Returns a PyObject from a 256-bits integer */
      PyObject* PyLong_FromUint256(triton::uint256 value) {
        PyLongObject* v;
        triton::uint256 t;
        int ndigits = 0;

        /* Count the number of Python digits. */
        t = value;
        while (t) {
          ++ndigits;
          t >>= PyLong_SHIFT;
        }

        v = _PyLong_New(ndigits);
        digit* p = v->ob_digit;
        Py_SIZE(v) = ndigits;
        while (value) {
          *p++ = (value & PyLong_MASK).convert_to<digit>();
          value >>= PyLong_SHIFT;
        }

        return (PyObject*)v;
      }


      /* Returns a PyObject from a 512-bits integer */
      PyObject* PyLong_FromUint512(triton::uint512 value) {
        PyLongObject* v;
        triton::uint512 t = 0;
        int ndigits = 0;

        /* Count the number of Python digits. */
        t = value;
        while (t) {
          ++ndigits;
          t >>= PyLong_SHIFT;
        }

        v = _PyLong_New(ndigits);
        digit* p = v->ob_digit;
        Py_SIZE(v) = ndigits;
        while (value) {
          *p++ = (value & PyLong_MASK).convert_to<digit>();
          value >>= PyLong_SHIFT;
        }

        return (PyObject*)v;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
