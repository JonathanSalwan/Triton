#include <string>

#include "pin.H"

#include "IRBuilderHeaders.h"
#include "PINConverter.h"


// Returns a pointer to an IRBuilder object.
// It is up to the user to delete it when times come.
IRBuilder *createIRBuilder(INS ins) {
  UINT64 address         = INS_Address(ins);
  std::string disas      = INS_Disassemble(ins);
  INT32 opcode           = INS_Opcode(ins);

  IRBuilder *ir = nullptr;

  switch (opcode) {

    case XED_ICLASS_ADC:
      ir = new AdcIRBuilder(address, disas);
      break;

    case XED_ICLASS_ADD:
      ir = new AddIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMP:
      ir = new CmpIRBuilder(address, disas);
      break;

    case XED_ICLASS_LEAVE:
      ir = new LeaveIRBuilder(address, disas);
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

    case XED_ICLASS_SBB:
      ir = new SbbIRBuilder(address, disas);
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
    IRBuilderOperand::operand_t   type;
    UINT32                        size = 0;
    UINT64                        val  = 0;

    if (INS_OperandIsImmediate(ins, i)) {
      type = IRBuilderOperand::IMM;
      val = INS_OperandImmediate(ins, i);
    }
    else if (INS_OperandIsReg(ins, i)) {
      type = IRBuilderOperand::REG;
      REG reg = INS_OperandReg(ins, i);
      val  = PINConverter::convertDBIReg2TritonReg(reg); // store the register ID.

      if (REG_valid(reg)) {
        // check needed because instructions like "xgetbv 0" make
        // REG_Size crash.
        size = REG_Size(reg);
      }
    }
    else if (INS_MemoryOperandCount(ins) > 0) {
      // check needed because instructions like "nop dword ptr [eax], ebx"
      // make INS_MemoryReadSize crash.

      if (INS_MemoryOperandIsRead(ins, 0)) {
        type = IRBuilderOperand::MEM_R;
        size = INS_MemoryReadSize(ins);
      }
      else {
        type = IRBuilderOperand::MEM_W;
        size = INS_MemoryWriteSize(ins);
      }
    }
    else
      continue;

    ir->addOperand(type, val, size);
  }

  // Setup the opcode in the IRbuilder
  ir->setOpcode(opcode);
  ir->setOpcodeCategory(INS_Category(ins));

  return ir;
}
