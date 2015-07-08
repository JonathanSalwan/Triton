
#include <TritonPyObject.h>
#include <xPyFunc.h>

/*
 * Class Operand
 *
 * - baseReg (IDREF.REG)
 * - displacement (integer)
 * - indexReg (IDREF.REG)
 * - memoryScale (integer)
 * - size (integer)
 * - type (IDREF.OPERAND)
 * - value (intger or IDREF.REG)
 */

PyObject *PyOperand(TritonOperand operand)
{
  PyObject *dictOperandClass = xPyDict_New();
  PyDict_SetItemString(dictOperandClass, "baseReg",       PyLong_FromLong(operand.getBaseReg()));
  PyDict_SetItemString(dictOperandClass, "displacement",  PyLong_FromLong(operand.getDisplacement()));
  PyDict_SetItemString(dictOperandClass, "indexReg",      PyLong_FromLong(operand.getIndexReg()));
  PyDict_SetItemString(dictOperandClass, "memoryScale",   PyLong_FromLong(operand.getMemoryScale()));
  PyDict_SetItemString(dictOperandClass, "size",          PyLong_FromLong(operand.getSize()));
  PyDict_SetItemString(dictOperandClass, "type",          PyLong_FromLong(operand.getType()));
  PyDict_SetItemString(dictOperandClass, "value",         PyLong_FromLong(operand.getValue()));

  /* Create the Operand class */
  PyObject *operandClassName = xPyString_FromString("Operand");
  PyObject *operandClass  = xPyClass_New(nullptr, dictOperandClass, operandClassName);

  Py_DECREF(dictOperandClass);
  Py_DECREF(operandClassName);
  Py_INCREF(operandClass);

  return operandClass;
}

