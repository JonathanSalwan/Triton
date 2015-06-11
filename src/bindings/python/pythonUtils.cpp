
#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <PythonUtils.h>


__uint128_t PyLongObjectToUint128(PyObject *value)
{
  __uint128_t v;
  uint64_t size = 0;
  uint64_t high = 0, low = 0;
  PyObject *hex = nullptr;
  PyObject *format = nullptr;
  PyObject *format_args = nullptr;

  format_args = Py_BuildValue("(O)", value);
  format = PyString_FromString("%x");
  hex = PyString_Format(format, format_args);

  PyObject* valueAsStr = PyObject_Str(hex);
  std::string stringValue(PyString_AsString(valueAsStr));

  size = stringValue.size();

  if (size > 32)
    throw std::runtime_error("Error: PyLongObjectToUint128() must be <= 128 bits");

  if (size <= 16){
    low = std::strtoul(stringValue.c_str(), nullptr, 16);
  }
  else {
    high = std::strtoul(stringValue.substr(0, size - 16).c_str(), nullptr, 16);
    low = std::strtoul(stringValue.substr(size - 16).c_str(), nullptr, 16);
  }

  v = high;
  v <<= 64;
  v |= low;

  Py_DECREF(valueAsStr);
  Py_DECREF(format_args);
  Py_DECREF(format);
  Py_DECREF(hex);

  return v;
}


PyObject *uint128ToPyLongObject(__uint128_t value)
{
  char tmp[32+1] = {0};
  uint64_t high = (value >> 64) & 0xffffffffffffffff;
  uint64_t low = value & 0xffffffffffffffff;
  snprintf(tmp, sizeof(tmp), "%lx%lx", high, low);
  return PyLong_FromString(tmp, nullptr, 16);
}

