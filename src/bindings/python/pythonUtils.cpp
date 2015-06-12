
#include <python2.7/Python.h>
#include <python2.7/longintrepr.h>

#include <PythonBindings.h>
#include <PythonUtils.h>

// Based on python-2.7/blob/master/Objects/longobject.c


__uint128_t PyLongObjectToUint128(PyObject *vv)
{
  register PyLongObject *v;
  __uint128_t x, prev;
  Py_ssize_t i;

  if (vv == NULL || !PyLong_Check(vv)) {
    if (vv != NULL && PyInt_Check(vv)) {
        __uint128_t val = PyInt_AsLong(vv);
        if (val < 0)
          throw std::runtime_error("Error: PyLongObjectToUint128() - can't convert negative value to unsigned long");
        return val;
    }
    throw std::runtime_error("Error: PyLongObjectToUint128() - Bad internal call");
  }

  v = (PyLongObject *)vv;
  i = Py_SIZE(v);
  x = 0;
  if (i < 0)
    throw std::runtime_error("Error: PyLongObjectToUint128() - can't convert negative value to unsigned long");

  while (--i >= 0) {
      prev = x;
      x = (x << PyLong_SHIFT) | v->ob_digit[i];
      if ((x >> PyLong_SHIFT) != prev)
          throw std::runtime_error("Error: PyLongObjectToUint128() - long int too large to convert");
  }

  return x;
}


PyObject *uint128ToPyLongObject(__uint128_t value)
{
  PyLongObject *v;
  __uint128_t t;
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
    *p++ = (digit)(value & PyLong_MASK);
    value >>= PyLong_SHIFT;
  }

  return (PyObject *)v;
}

