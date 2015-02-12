#include <iostream>
#include <string>

#include "pin.H"

#include "IRBuilderFactory.h"
#include "MovIRBuilder.h"
#include "NullIRBuilder.h"

// Returns a pointer to a IRBuilder object.
// It is up to the user to delete it when times come.
IRBuilder *createIRBuilder(INS ins) {
  UINT64 address = INS_Address(ins);
  std::string disas = INS_Disassemble(ins);
  INT32 opcode = INS_Opcode(ins);

  IRBuilder *ir = NULL;

  switch (opcode) {

    case XED_ICLASS_MOVSX:
    case XED_ICLASS_MOVZX:
    case XED_ICLASS_MOV:
      ir = new MovIRBuilder(address, disas);

      break;

    default:
      ir = new NullIRBuilder(address, disas);
  }

  // Populate the operands
  const UINT32 n = INS_OperandCount(ins);

  for (UINT32 i = 0; i < n; ++i) {
    IRBuilder::operand_t type;
    UINT64 val = 0;

    if (INS_OperandIsImmediate(ins, i)) {
      type = IRBuilder::IMM;
      val = INS_OperandImmediate(ins, i);
    }
    else if (INS_OperandIsReg(ins, i)) {
      type = IRBuilder::REG;
      val = INS_OperandReg(ins, i);
    }
    else if (INS_MemoryOperandIsRead(ins, 0))
      type = IRBuilder::MEM_R;
    else if (INS_MemoryOperandIsWritten(ins, 0))
      type = IRBuilder::MEM_W;
    else
      continue;

    ir->addOperand(type, val);
  }

  return ir;
}
