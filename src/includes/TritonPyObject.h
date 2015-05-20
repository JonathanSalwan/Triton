
#ifndef   __TRITONPYOBJECT_H__
#define   __TRITONPYOBJECT_H__

#include <python2.7/Python.h>
#include "IRBuilder.h"
#include "IRBuilderOperand.h"
#include "Inst.h"
#include "SymbolicEngine.h"
#include "TritonOperand.h"


PyObject *PyInstruction(IRBuilder *irb);
PyObject *PyInstruction(Inst *inst);
PyObject *PyOperand(TritonOperand operand);
PyObject *PySymbolicElement(SymbolicElement *element);


#endif     /* !__TRITONPYOBJECT_H__ */

