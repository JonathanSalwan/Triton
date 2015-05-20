
#ifndef   __TRITONPYOBJECT_H__
#define   __TRITONPYOBJECT_H__

#include <python2.7/Python.h>
#include "IRBuilder.h"
#include "Inst.h"
#include "SymbolicEngine.h"
#include "IRBuilderOperand.h"


PyObject *PyInstruction(IRBuilder *irb);
PyObject *PyInstruction(Inst *inst);
PyObject *PyOperand(std::tuple<IRBuilderOperand::operand_t, uint64_t, uint32_t, uint64_t, uint64_t, uint64_t, uint64_t> operand);
PyObject *PySymbolicElement(SymbolicElement *element);


#endif     /* !__TRITONPYOBJECT_H__ */

