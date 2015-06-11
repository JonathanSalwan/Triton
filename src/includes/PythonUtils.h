#ifndef   PYTHONUTILS_H
#define   PYTHONUTILS_H

#include <cstdint>
#include <python2.7/Python.h>

__uint128_t   PyLongObjectToUint128(PyObject *obj);
PyObject      *uint128ToPyLongObject(__uint128_t value);

#endif     /* !PYTHONUTILS_H */
