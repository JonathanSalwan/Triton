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

    case XED_ICLASS_AND:
      ir = new AndIRBuilder(address, disas);
      break;

    case XED_ICLASS_CALL_FAR:
    case XED_ICLASS_CALL_NEAR:
      ir = new CallIRBuilder(address, disas);
      break;

    case XED_ICLASS_CLC:
      ir = new ClcIRBuilder(address, disas);
      break;

    case XED_ICLASS_CLD:
      ir = new CldIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMC:
      ir = new CmcIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMP:
      ir = new CmpIRBuilder(address, disas);
      break;

    case XED_ICLASS_DEC:
      ir = new DecIRBuilder(address, disas);
      break;

    case XED_ICLASS_INC:
      ir = new IncIRBuilder(address, disas);
      break;

    case XED_ICLASS_JB:
      ir = new JbIRBuilder(address, disas);
      break;

    case XED_ICLASS_JNB:
      ir = new JnbIRBuilder(address, disas);
      break;

    case XED_ICLASS_JNP:
      ir = new JnpIRBuilder(address, disas);
      break;

    case XED_ICLASS_JNS:
      ir = new JnsIRBuilder(address, disas);
      break;

    case XED_ICLASS_JNZ:
      ir = new JnzIRBuilder(address, disas);
      break;

    case XED_ICLASS_JS:
      ir = new JsIRBuilder(address, disas);
      break;

    case XED_ICLASS_JZ:
      ir = new JzIRBuilder(address, disas);
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

    case XED_ICLASS_NOT:
      ir = new NotIRBuilder(address, disas);
      break;

    case XED_ICLASS_OR:
      ir = new OrIRBuilder(address, disas);
      break;

    case XED_ICLASS_POP:
      ir = new PopIRBuilder(address, disas);
      break;

    case XED_ICLASS_PUSH:
      ir = new PushIRBuilder(address, disas);
      break;

    case XED_ICLASS_RET_FAR:
    case XED_ICLASS_RET_NEAR:
      ir = new RetIRBuilder(address, disas);
      break;

    case XED_ICLASS_SBB:
      ir = new SbbIRBuilder(address, disas);
      break;

    case XED_ICLASS_STC:
      ir = new StcIRBuilder(address, disas);
      break;

    case XED_ICLASS_STD:
      ir = new StdIRBuilder(address, disas);
      break;

    case XED_ICLASS_SUB:
      ir = new SubIRBuilder(address, disas);
      break;

    case XED_ICLASS_TEST:
      ir = new TestIRBuilder(address, disas);
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

    /* Special case */
    if (INS_IsDirectBranchOrCall(ins)){
      ir->addOperand(IRBuilderOperand::IMM, INS_DirectBranchOrCallTargetAddress(ins), 0);
      if (INS_MemoryOperandIsWritten(ins, 0))
        ir->addOperand(IRBuilderOperand::MEM_W, 0, INS_MemoryWriteSize(ins));
      break;
    }

    /* Immediate */
    if (INS_OperandIsImmediate(ins, i)) {
      type = IRBuilderOperand::IMM;
      val = INS_OperandImmediate(ins, i);
    }

    /* Register */
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

    /* Memory */
    else if (INS_MemoryOperandCount(ins) > 0) {
      /* Memory read */
      if (INS_MemoryOperandIsRead(ins, 0)) {
        type = IRBuilderOperand::MEM_R;
        size = INS_MemoryReadSize(ins);
      }
      /* Memory write */
      else {
        type = IRBuilderOperand::MEM_W;
        size = INS_MemoryWriteSize(ins);
      }
    }
    // TODO: Effective address = Displacement + BaseReg + IndexReg * Scale
    /* Undefined */
    else {
      //std::cout << "[DEBUG] Unknown kind of operand: " << INS_Disassemble(ins) << std::endl;
      continue;
    }

    ir->addOperand(type, val, size);
  }

  // Setup the opcode in the IRbuilder
  ir->setOpcode(opcode);
  ir->setOpcodeCategory(INS_Category(ins));
  ir->setNextAddress(INS_NextAddress(ins));

  return ir;
}
