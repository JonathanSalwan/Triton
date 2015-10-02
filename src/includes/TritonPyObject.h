/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#ifndef   TRITONPYOBJECT_H
#define   TRITONPYOBJECT_H

#include <python2.7/Python.h>
#include "IRBuilder.h"
#include "IRBuilderOperand.h"
#include "Inst.h"

#ifndef LIGHT_VERSION
  #include "SMT2Lib.h"
  #include "SymbolicEngine.h"
  #include "SymbolicVariable.h"
  #include "TritonOperand.h"
#endif


PyObject *PyInstruction(IRBuilder *irb);
PyObject *PyInstruction(Inst *inst);
PyObject *PyOperand(TritonOperand operand);
PyObject *PyRegisterOperand(RegisterOperand reg);
PyObject *PyMemoryOperand(MemoryOperand mem);
PyObject *PyImmediateOperand(ImmediateOperand imm);

#ifndef LIGHT_VERSION
PyObject *PySmtAstNode(smt2lib::smtAstAbstractNode *node);
PyObject *PySymbolicExpression(SymbolicExpression *expression);
PyObject *PySymbolicVariable(SymbolicVariable *symVar);

// SmtAstNode ===================================

typedef struct {
  PyObject_HEAD
  smt2lib::smtAstAbstractNode *node;
} SmtAstNode_Object;

extern PyTypeObject SmtAstNode_Type;

#define PySmtAstNode_Check(v) ((v)->ob_type == &SmtAstNode_Type)
#define PySmtAstNode_AsSmtAstNode(v) (((SmtAstNode_Object *)(v))->node)

// SymbolicExpression ===========================

typedef struct {
  PyObject_HEAD
  SymbolicExpression *expression;
} SymbolicExpression_Object;

extern PyTypeObject SymbolicExpression_Type;

#define PySymbolicExpression_Check(v) ((v)->ob_type == &SymbolicExpression_Type)
#define PySymbolicExpression_AsSymbolicExpression(v) (((SymbolicExpression_Object *)(v))->expression)

// SymbolicVariable =============================

typedef struct {
  PyObject_HEAD
  SymbolicVariable *variable;
} SymbolicVariable_Object;

extern PyTypeObject SymbolicVariable_Type;

#define PySymbolicVariable_Check(v) ((v)->ob_type == &SymbolicVariable_Type)
#define PySymbolicVariable_AsSymbolicVariable(v) (((SymbolicVariable_Object *)(v))->variable)

#endif /* LIGHT_VERSION */

// Operand =============================

typedef struct {
  PyObject_HEAD
  TritonOperand *operand;
} Operand_Object;

extern PyTypeObject Operand_Type;

#define PyOperand_Check(v) ((v)->ob_type == &Operand_Type)
#define PyOperand_AsOperand(v) (((Operand_Object *)(v))->operand)

// Instruction =============================

typedef struct {
  PyObject_HEAD
  IRBuilder *irb;
  Inst      *ins;
} Instruction_Object;

extern PyTypeObject Instruction_Type;

#define PyInstruction_Check(v) ((v)->ob_type == &Instruction_Type)
#define PyInstruction_AsIns(v) (((Instruction_Object *)(v))->ins)
#define PyInstruction_AsIrb(v) (((Instruction_Object *)(v))->irb)

// RegisterOperand =============================

typedef struct {
  PyObject_HEAD
  RegisterOperand *reg;
} RegisterOperand_Object;

extern PyTypeObject RegisterOperand_Type;

#define PyRegisterOperand_Check(v) ((v)->ob_type == &RegisterOperand_Type)
#define PyRegisterOperand_AsRegisterOperand(v) (((RegisterOperand_Object *)(v))->reg)

// MemoryOperand =============================

typedef struct {
  PyObject_HEAD
  MemoryOperand *mem;
} MemoryOperand_Object;

extern PyTypeObject MemoryOperand_Type;

#define PyMemoryOperand_Check(v) ((v)->ob_type == &MemoryOperand_Type)
#define PyMemoryOperand_AsMemoryOperand(v) (((MemoryOperand_Object *)(v))->mem)

// ImmediateOperand =============================

typedef struct {
  PyObject_HEAD
  ImmediateOperand *imm;
} ImmediateOperand_Object;

extern PyTypeObject ImmediateOperand_Type;

#define PyImmediateOperand_Check(v) ((v)->ob_type == &ImmediateOperand_Type)
#define PyImmediateOperand_AsImmediateOperand(v) (((ImmediateOperand_Object *)(v))->imm)

#endif     /* !__TRITONPYOBJECT_H__ */

