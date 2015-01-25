
#include "pin.H"
#include "triton.h"



VOID Instruction(INS ins, VOID *v)
{
  INT32 opcode;

  opcode = INS_Opcode(ins);

  switch (opcode) {

    case XED_ICLASS_MOVSX:
    case XED_ICLASS_MOVZX:
    case XED_ICLASS_MOV:

      /* mov reg, reg */
      if (INS_OperandCount(ins) == 2 && INS_OperandIsReg(ins, 0) && INS_OperandIsReg(ins, 1))
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)movRegReg,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_CONTEXT,
          IARG_UINT32, INS_OperandReg(ins, 0),
          IARG_UINT32, INS_OperandReg(ins, 1),
          IARG_UINT32, opcode,
          IARG_END);

      /* mov reg, imm */
      else if (INS_OperandCount(ins) == 2 && INS_OperandIsReg(ins, 0) && INS_OperandIsImmediate(ins, 1))
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)movRegImm,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_UINT32, INS_OperandReg(ins, 0),
          IARG_ADDRINT, INS_OperandImmediate(ins, 1),
          IARG_UINT32, opcode,
          IARG_END);

      /* mov reg, [mem] */
      else if (INS_OperandCount(ins) == 2 && INS_MemoryOperandIsRead(ins, 0) && INS_OperandIsReg(ins, 0))
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)movRegMem,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_UINT32, INS_OperandReg(ins, 0),
          IARG_MEMORYOP_EA, 0,
          IARG_UINT32, INS_MemoryReadSize(ins),
          IARG_UINT32, opcode,
          IARG_END);

      /* mov [mem], reg */
      else if (INS_OperandCount(ins) == 2 && INS_MemoryOperandIsWritten(ins, 0) && INS_OperandIsReg(ins, 1))
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)movMemReg,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_CONTEXT, 
          IARG_UINT32, INS_OperandReg(ins, 1),
          IARG_MEMORYOP_EA, 0,
          IARG_UINT32, INS_MemoryWriteSize(ins),
          IARG_UINT32, opcode,
          IARG_END);

      /* mov [mem], imm */
      else if (INS_OperandCount(ins) == 2 && INS_MemoryOperandIsWritten(ins, 0) && INS_OperandIsImmediate(ins, 1))
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)movMemImm,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_UINT32, INS_OperandImmediate(ins, 1),
          IARG_MEMORYOP_EA, 0,
          IARG_UINT32, INS_MemoryWriteSize(ins),
          IARG_UINT32, opcode,
          IARG_END);

      else
        /* Callback for semantics not yet implemented */
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)notImplemented,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_END);

      break;

    case XED_ICLASS_PUSH:

      /* push reg */
      if (INS_OperandCount(ins) == 4 && INS_OperandIsReg(ins, 0))
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)pushReg,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_CONTEXT, 
          IARG_UINT32, INS_OperandReg(ins, 0),
          IARG_MEMORYOP_EA, 0,
          IARG_UINT32, INS_MemoryWriteSize(ins),
          IARG_END);

      /* push imm */
      else if (INS_OperandCount(ins) == 4 && INS_OperandIsImmediate(ins, 0))
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)pushImm,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_CONTEXT, 
          IARG_ADDRINT, INS_OperandImmediate(ins, 0),
          IARG_MEMORYOP_EA, 0,
          IARG_UINT32, INS_MemoryWriteSize(ins),
          IARG_END);

      else
        /* Callback for semantics not yet implemented */
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)notImplemented,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_END);

      break;

    case XED_ICLASS_POP:

      if (INS_OperandCount(ins) == 4 && INS_OperandIsReg(ins, 0))
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)popReg,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_CONTEXT, 
          IARG_UINT32, INS_OperandReg(ins, 0),
          IARG_MEMORYOP_EA, 0,
          IARG_UINT32, INS_MemoryReadSize(ins),
          IARG_END);

      else
        /* Callback for semantics not yet implemented */
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)notImplemented,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_END);

      break;

    case XED_ICLASS_ADD:

      /* add reg, imm */
      if (INS_OperandCount(ins) == 3 && INS_OperandIsReg(ins, 0) && INS_OperandIsImmediate(ins, 1))
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)addRegImm,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_CONTEXT,
          IARG_UINT32, INS_OperandReg(ins, 0),
          IARG_ADDRINT, INS_OperandImmediate(ins, 1),
          IARG_END);

      /* add reg, reg */
      else if (INS_OperandCount(ins) == 3 && INS_OperandIsReg(ins, 0) && INS_OperandIsReg(ins, 1))
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)addRegReg,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_CONTEXT,
          IARG_UINT32, INS_OperandReg(ins, 0),
          IARG_UINT32, INS_OperandReg(ins, 1),
          IARG_END);

      else
        /* Callback for semantics not yet implemented */
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)notImplemented,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_END);

      break;

    case XED_ICLASS_CMP:

      /* cmp reg, imm */
      if (INS_OperandCount(ins) == 3 && INS_OperandIsReg(ins, 0) && INS_OperandIsImmediate(ins, 1))
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)cmpRegImm,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_CONTEXT,
          IARG_UINT32, INS_OperandReg(ins, 0),
          IARG_ADDRINT, INS_OperandImmediate(ins, 1),
          IARG_END);

      /* cmp reg, reg */
      else if (INS_OperandCount(ins) == 3 && INS_OperandIsReg(ins, 0) && INS_OperandIsReg(ins, 1))
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)cmpRegReg,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_CONTEXT,
          IARG_UINT32, INS_OperandReg(ins, 0),
          IARG_UINT32, INS_OperandReg(ins, 1),
          IARG_END);

      /* cmp [mem], imm */
      else if (INS_OperandCount(ins) == 3 && INS_MemoryOperandIsRead(ins, 0) && INS_OperandIsImmediate(ins, 1))
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)cmpMemImm,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_UINT32, INS_OperandImmediate(ins, 1),
          IARG_MEMORYOP_EA, 0,
          IARG_UINT32, INS_MemoryReadSize(ins),
          IARG_END);

      else
        /* Callback for semantics not yet implemented */
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)notImplemented,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_END);

      break;

    case XED_ICLASS_JZ:
    case XED_ICLASS_JNZ:

        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)branchs,
          IARG_PTR, new string(INS_Disassemble(ins)),
          IARG_ADDRINT, INS_Address(ins),
          IARG_CONTEXT,
          IARG_UINT32, opcode,
          IARG_END);

      break;

    default:

      /* Callback for semantics not yet implemented */
      INS_InsertCall(
        ins, IPOINT_BEFORE, (AFUNPTR)notImplemented,
        IARG_PTR, new string(INS_Disassemble(ins)),
        IARG_ADDRINT, INS_Address(ins),
        IARG_END);

      break;
  }
}
