#ifndef   PYTHONUTILS_H
#define   PYTHONUTILS_H

#include "TritonTypes.h"
#include <python2.7/Python.h>

uint128   PyLongObjectToUint128(PyObject *obj);
PyObject      *uint128ToPyLongObject(uint128 value);

#endif     /* !PYTHONUTILS_H */
