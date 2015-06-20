
#include <stdexcept>

#include <python2.7/Python.h>
#include <python2.7/longintrepr.h>

#include <PythonBindings.h>
#include <PythonUtils.h>

// Based on python-2.7/blob/master/Objects/longobject.c


uint128 PyLongObjectToUint128(PyObject *vv)
{
  register PyLongObject *v;
  uint128 x, prev;
  Py_ssize_t i;

  if (vv == NULL || !PyLong_Check(vv)) {
    if (vv != NULL && PyInt_Check(vv)) {
        uint128 val = PyInt_AsLong(vv);
        if (val < 0)
          throw std::runtime_error("Error: PyLongObjectToUint128() - can't convert negative value to unsigned long");
        return val;
    }
    throw std::runtime_error("Error: PyLongObjectToUint128() - Bad internal call");
  }

  v = reinterpret_cast<PyLongObject *>(vv);
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


PyObject *uint128ToPyLongObject(uint128 value)
{
  PyLongObject *v;
  uint128 t;
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

  return (PyObject *)v;
}

