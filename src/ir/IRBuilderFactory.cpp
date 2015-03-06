#include <string>

#include "pin.H"

#include "AddIRBuilder.h"
#include "CmpIRBuilder.h"
#include "IRBuilderFactory.h"
#include "MovIRBuilder.h"
#include "MovsxIRBuilder.h"
#include "MovzxIRBuilder.h"
#include "NullIRBuilder.h"
#include "PopIRBuilder.h"
#include "PushIRBuilder.h"
#include "SubIRBuilder.h"
#include "XorIRBuilder.h"


// Returns a pointer to an IRBuilder object.
// It is up to the user to delete it when times come.
IRBuilder *createIRBuilder(INS ins) {
  UINT64 address    = INS_Address(ins);
  std::string disas = INS_Disassemble(ins);
  INT32 opcode      = INS_Opcode(ins);

  IRBuilder *ir = NULL;

  switch (opcode) {

    case XED_ICLASS_ADD:
      ir = new AddIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMP:
      ir = new CmpIRBuilder(address, disas);
      break;

    case XED_ICLASS_MOV:
      ir = new MovIRBuilder(address, disas);
      break;

    case XED_ICLASS_MOVSX:
    case XED_ICLASS_MOVSXD:
      ir = new MovsxIRBuilder(address, disas);
      break;

    case XED_ICLASS_MOVZX:
      ir = new MovzxIRBuilder(address, disas);
      break;

    case XED_ICLASS_POP:
      ir = new PopIRBuilder(address, disas);
      break;

    case XED_ICLASS_PUSH:
      ir = new PushIRBuilder(address, disas);
      break;

    case XED_ICLASS_SUB:
      ir = new SubIRBuilder(address, disas);
      break;

    case XED_ICLASS_XOR:
      ir = new XorIRBuilder(address, disas);
      break;

    default:
      ir = new NullIRBuilder(address, disas);
      break;
  }

  // Populate the operands
  const UINT32 n = INS_OperandCount(ins);

  for (UINT32 i = 0; i < n; ++i) {
    IRBuilder::operand_t  type;
    UINT32                size = 0;
    UINT64                val  = 0;

    if (INS_OperandIsImmediate(ins, i)) {
      type = IRBuilder::IMM;
      val = INS_OperandImmediate(ins, i);
    }
    else if (INS_OperandIsReg(ins, i)) {
      type = IRBuilder::REG;
      val  = INS_OperandReg(ins, i);
    }
    else if (INS_MemoryOperandCount(ins) > 0) {
      // check needed because instructions like "nop dword ptr [eax], ebx"
      // makes INS_MemoryReadSize crash.

      if (INS_MemoryOperandIsRead(ins, 0)) {
        type = IRBuilder::MEM_R;
        size = INS_MemoryReadSize(ins);
      }
      else {
        type = IRBuilder::MEM_W;
        size = INS_MemoryWriteSize(ins);
      }
    }
    else
      continue;

    ir->addOperand(type, val, size);
  }

  return ir;
}

