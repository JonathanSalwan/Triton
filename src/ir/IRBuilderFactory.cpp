/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <string>

#include <pin.H>

#include <IRBuilderHeaders.h>
#include <PINConverter.h>


// Returns a pointer to an IRBuilder object.
// It is up to the user to delete it when times come.
IRBuilder *createIRBuilder(INS ins) {

  uint64 address         = INS_Address(ins);
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

    case XED_ICLASS_ANDNPD:
      ir = new AndnpdIRBuilder(address, disas);
      break;

    case XED_ICLASS_ANDNPS:
      ir = new AndnpsIRBuilder(address, disas);
      break;

    case XED_ICLASS_ANDPD:
      ir = new AndpdIRBuilder(address, disas);
      break;

    case XED_ICLASS_ANDPS:
      ir = new AndpsIRBuilder(address, disas);
      break;

    case XED_ICLASS_BSWAP:
      ir = new BswapIRBuilder(address, disas);
      break;

    case XED_ICLASS_CALL_FAR:
    case XED_ICLASS_CALL_NEAR:
      ir = new CallIRBuilder(address, disas);
      break;

    case XED_ICLASS_CBW:
      ir = new CbwIRBuilder(address, disas);
      break;

    case XED_ICLASS_CDQE:
      ir = new CdqeIRBuilder(address, disas);
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

    case XED_ICLASS_CMOVB:
      ir = new CmovbIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMOVBE:
      ir = new CmovbeIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMOVL:
      ir = new CmovlIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMOVLE:
      ir = new CmovleIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMOVNB:
      ir = new CmovnbIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMOVNBE:
      ir = new CmovnbeIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMOVNL:
      ir = new CmovnlIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMOVNLE:
      ir = new CmovnleIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMOVNO:
      ir = new CmovnoIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMOVNP:
      ir = new CmovnpIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMOVNS:
      ir = new CmovnsIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMOVNZ:
      ir = new CmovnzIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMOVO:
      ir = new CmovoIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMOVP:
      ir = new CmovpIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMOVS:
      ir = new CmovsIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMOVZ:
      ir = new CmovzIRBuilder(address, disas);
      break;

    case XED_ICLASS_CMP:
      ir = new CmpIRBuilder(address, disas);
      break;

    case XED_ICLASS_CQO:
      ir = new CqoIRBuilder(address, disas);
      break;

    case XED_ICLASS_CWDE:
      ir = new CwdeIRBuilder(address, disas);
      break;

    case XED_ICLASS_DEC:
      ir = new DecIRBuilder(address, disas);
      break;

    case XED_ICLASS_DIV:
      ir = new DivIRBuilder(address, disas);
      break;

    case XED_ICLASS_IDIV:
      ir = new IdivIRBuilder(address, disas);
      break;

    case XED_ICLASS_IMUL:
      ir = new ImulIRBuilder(address, disas);
      break;

    case XED_ICLASS_INC:
      ir = new IncIRBuilder(address, disas);
      break;

    case XED_ICLASS_JB:
      ir = new JbIRBuilder(address, disas);
      break;

    case XED_ICLASS_JBE:
      ir = new JbIRBuilder(address, disas);
      break;

    case XED_ICLASS_JL:
      ir = new JlIRBuilder(address, disas);
      break;

    case XED_ICLASS_JLE:
      ir = new JleIRBuilder(address, disas);
      break;

    case XED_ICLASS_JMP:
      ir = new JmpIRBuilder(address, disas);
      break;

    case XED_ICLASS_JNB:
      ir = new JnbIRBuilder(address, disas);
      break;

    case XED_ICLASS_JNBE:
      ir = new JnbeIRBuilder(address, disas);
      break;

    case XED_ICLASS_JNL:
      ir = new JnlIRBuilder(address, disas);
      break;

    case XED_ICLASS_JNLE:
      ir = new JnleIRBuilder(address, disas);
      break;

    case XED_ICLASS_JNO:
      ir = new JnoIRBuilder(address, disas);
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

    case XED_ICLASS_JO:
      ir = new JoIRBuilder(address, disas);
      break;

    case XED_ICLASS_JP:
      ir = new JpIRBuilder(address, disas);
      break;

    case XED_ICLASS_JS:
      ir = new JsIRBuilder(address, disas);
      break;

    case XED_ICLASS_JZ:
      ir = new JzIRBuilder(address, disas);
      break;

    case XED_ICLASS_LEA:
      ir = new LeaIRBuilder(address, disas);
      break;

    case XED_ICLASS_LEAVE:
      ir = new LeaveIRBuilder(address, disas);
      break;

    case XED_ICLASS_MOV:
      ir = new MovIRBuilder(address, disas);
      break;

    case XED_ICLASS_MOVAPD:
      ir = new MovapdIRBuilder(address, disas);
      break;

    case XED_ICLASS_MOVAPS:
      ir = new MovapsIRBuilder(address, disas);
      break;

    case XED_ICLASS_MOVDQA:
      ir = new MovdqaIRBuilder(address, disas);
      break;

    case XED_ICLASS_MOVDQU:
      ir = new MovdquIRBuilder(address, disas);
      break;

    case XED_ICLASS_MOVHLPS:
      ir = new MovhlpsIRBuilder(address, disas);
      break;

    case XED_ICLASS_MOVHPD:
      ir = new MovhpdIRBuilder(address, disas);
      break;

    case XED_ICLASS_MOVHPS:
      ir = new MovhpsIRBuilder(address, disas);
      break;

    case XED_ICLASS_MOVLHPS:
      ir = new MovlhpsIRBuilder(address, disas);
      break;

    case XED_ICLASS_MOVLPD:
      ir = new MovlpdIRBuilder(address, disas);
      break;

    case XED_ICLASS_MOVLPS:
      ir = new MovlpsIRBuilder(address, disas);
      break;

    case XED_ICLASS_MOVSX:
    case XED_ICLASS_MOVSXD:
      ir = new MovsxIRBuilder(address, disas);
      break;

    case XED_ICLASS_MOVZX:
      ir = new MovzxIRBuilder(address, disas);
      break;

    case XED_ICLASS_MUL:
      ir = new MulIRBuilder(address, disas);
      break;

    case XED_ICLASS_NEG:
      ir = new NegIRBuilder(address, disas);
      break;

    case XED_ICLASS_NOT:
      ir = new NotIRBuilder(address, disas);
      break;

    case XED_ICLASS_OR:
      ir = new OrIRBuilder(address, disas);
      break;

    case XED_ICLASS_ORPD:
      ir = new OrpdIRBuilder(address, disas);
      break;

    case XED_ICLASS_ORPS:
      ir = new OrpsIRBuilder(address, disas);
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

    case XED_ICLASS_RCL:
      ir = new RclIRBuilder(address, disas);
      break;

    case XED_ICLASS_ROL:
      ir = new RolIRBuilder(address, disas);
      break;

    case XED_ICLASS_RCR:
      ir = new RcrIRBuilder(address, disas);
      break;

    case XED_ICLASS_ROR:
      ir = new RorIRBuilder(address, disas);
      break;

    case XED_ICLASS_SAR:
      ir = new SarIRBuilder(address, disas);
      break;

    case XED_ICLASS_SBB:
      ir = new SbbIRBuilder(address, disas);
      break;

    case XED_ICLASS_SETB:
      ir = new SetbIRBuilder(address, disas);
      break;

    case XED_ICLASS_SETBE:
      ir = new SetbeIRBuilder(address, disas);
      break;

    case XED_ICLASS_SETL:
      ir = new SetlIRBuilder(address, disas);
      break;

    case XED_ICLASS_SETLE:
      ir = new SetleIRBuilder(address, disas);
      break;

    case XED_ICLASS_SETNB:
      ir = new SetnbIRBuilder(address, disas);
      break;

    case XED_ICLASS_SETNBE:
      ir = new SetnbeIRBuilder(address, disas);
      break;

    case XED_ICLASS_SETNL:
      ir = new SetnlIRBuilder(address, disas);
      break;

    case XED_ICLASS_SETNLE:
      ir = new SetnleIRBuilder(address, disas);
      break;

    case XED_ICLASS_SETNO:
      ir = new SetnoIRBuilder(address, disas);
      break;

    case XED_ICLASS_SETNP:
      ir = new SetnpIRBuilder(address, disas);
      break;

    case XED_ICLASS_SETNS:
      ir = new SetnsIRBuilder(address, disas);
      break;

    case XED_ICLASS_SETNZ:
      ir = new SetnzIRBuilder(address, disas);
      break;

    case XED_ICLASS_SETO:
      ir = new SetoIRBuilder(address, disas);
      break;

    case XED_ICLASS_SETP:
      ir = new SetpIRBuilder(address, disas);
      break;

    case XED_ICLASS_SETS:
      ir = new SetsIRBuilder(address, disas);
      break;

    case XED_ICLASS_SETZ:
      ir = new SetzIRBuilder(address, disas);
      break;

    case XED_ICLASS_SHL:
      // XED_ICLASS_SAL is also a SHL
      ir = new ShlIRBuilder(address, disas);
      break;

    case XED_ICLASS_SHR:
      ir = new ShrIRBuilder(address, disas);
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

    case XED_ICLASS_XADD:
      ir = new XaddIRBuilder(address, disas);
      break;

    case XED_ICLASS_XCHG:
      ir = new XchgIRBuilder(address, disas);
      break;

    case XED_ICLASS_XOR:
      ir = new XorIRBuilder(address, disas);
      break;

    case XED_ICLASS_XORPD:
      ir = new XorpdIRBuilder(address, disas);
      break;

    case XED_ICLASS_XORPS:
      ir = new XorpsIRBuilder(address, disas);
      break;

    default:
      ir = new NullIRBuilder(address, disas);
      break;
  }

  /* Populate the operands */
  const uint32 n = INS_OperandCount(ins);

  for (uint32 i = 0; i < n; ++i) {

    TritonOperand op;

    /* Special case */
    if (INS_IsDirectBranchOrCall(ins)){

      TritonOperand op1;
      op1.setType(IRBuilderOperand::IMM);
      op1.setValue(INS_DirectBranchOrCallTargetAddress(ins));
      ir->addOperand(op1);

      if (INS_MemoryOperandIsWritten(ins, 0)) {
        TritonOperand op2;
        op2.setType(IRBuilderOperand::MEM_W);
        op2.setSize(INS_MemoryWriteSize(ins));
        ir->addOperand(op2);
      }

      break;
    }

    /* Immediate */
    if (INS_OperandIsImmediate(ins, i)) {
      op.setType(IRBuilderOperand::IMM);
      op.setValue(INS_OperandImmediate(ins, i));
    }

    /* Register */
    else if (INS_OperandIsReg(ins, i)) {
      REG reg = INS_OperandReg(ins, i);
      op.setType(IRBuilderOperand::REG);
      op.setValue(PINConverter::convertDBIReg2TritonReg(reg));
      if (REG_valid(reg)) {
        // check needed because instructions like "xgetbv 0" make
        // REG_Size crash.
        op.setSize(REG_Size(reg));
      }
    }

    /* Memory */
    else if (INS_MemoryOperandCount(ins) > 0) {
      /* Memory read */
      if (INS_MemoryOperandIsRead(ins, 0)) {
        op.setType(IRBuilderOperand::MEM_R);
        op.setSize(INS_MemoryReadSize(ins));
      }
      /* Memory write */
      else {
        op.setType(IRBuilderOperand::MEM_W);
        op.setSize(INS_MemoryWriteSize(ins));
      }
    }

    /* load effective address instruction */
    else if (INS_OperandIsAddressGenerator(ins, i)) {
      REG reg;
      op.setType(IRBuilderOperand::LEA);
      op.setDisplacement(INS_OperandMemoryDisplacement(ins, i));
      op.setMemoryScale(INS_OperandMemoryScale(ins, i));

      reg = INS_OperandMemoryBaseReg(ins, i);
      if (REG_valid(reg))
        op.setBaseReg(PINConverter::convertDBIReg2TritonReg(reg));

      reg = INS_OperandMemoryIndexReg(ins, i);
      if (REG_valid(reg))
        op.setIndexReg(PINConverter::convertDBIReg2TritonReg(reg));
    }

    /* Undefined */
    else {
      // std::cout << "[DEBUG] Unknown kind of operand: " << INS_Disassemble(ins) << std::endl;
      continue;
    }

    op.setReadAndWrite(INS_OperandReadAndWritten(ins, i));
    op.setReadOnly(INS_OperandReadOnly(ins, i));
    op.setWriteOnly(INS_OperandWrittenOnly(ins, i));
    ir->addOperand(op);

  }

  // Setup the opcode in the IRbuilder
  ir->setOpcode(opcode);
  ir->setOpcodeCategory(INS_Category(ins));
  ir->setNextAddress(INS_NextAddress(ins));

  return ir;
}
