/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef   PYTHONUTILS_H
#define   PYTHONUTILS_H

#include "TritonTypes.h"
#include <python2.7/Python.h>

uint128   PyLongObjectToUint128(PyObject *obj);
PyObject      *uint128ToPyLongObject(uint128 value);
PyObject      *uint512ToPyLongObject(uint512 value);

#endif     /* !PYTHONUTILS_H */
