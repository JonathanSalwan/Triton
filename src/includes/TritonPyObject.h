
#ifndef   __TRITONPYOBJECT_H__
#define   __TRITONPYOBJECT_H__

#include <python2.7/Python.h>
#include "IRBuilder.h"
#include "Inst.h"
#include "SymbolicEngine.h"


PyObject *PySymbolicElement(SymbolicElement *element);
PyObject *PyInstruction(Inst *inst);
PyObject *PyInstruction(IRBuilder *irb);


#endif     /* !__TRITONPYOBJECT_H__ */

