
#include "pin.H"
#include "triton.h"


VOID movRegReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, REG reg2, INT32 opcode)
{
  if (_analysisStatus == LOCKED)
    return;

  std::stringstream src, dst, taint;

  UINT64 reg1_ID  = translatePinRegToID(reg1);
  UINT64 reg2_ID  = translatePinRegToID(reg2);
  UINT64 size     = (REG_Size(reg1) * 8) - (REG_Size(reg2) * 8);

  dst << "#" << std::dec << uniqueID;

  if (symbolicReg[reg2_ID] != (UINT64)-1){
    switch(opcode){
      case XED_ICLASS_MOV:
        src << "#" << std::dec << symbolicReg[reg2_ID];
        break;
      case XED_ICLASS_MOVSX:
        src << "SignExt(" << std::dec << size << ", #" << symbolicReg[reg2_ID] << ")";
        break;
      case XED_ICLASS_MOVZX:
        src << "ZeroExt(" << std::dec << size << ", #" << symbolicReg[reg2_ID] << ")";
        break;
    }
  }
  else{
    switch(opcode){
      case XED_ICLASS_MOV:
        src << "0x" << std::hex << PIN_GetContextReg(ctx, getHighReg(reg2));
        break;
      case XED_ICLASS_MOVSX:
        src << "SignExt(" << std::dec << size << ", 0x" << std::hex << PIN_GetContextReg(ctx, getHighReg(reg2)) << ")";
        break;
      case XED_ICLASS_MOVZX:
        src << "ZeroExt(" << std::dec << size << ", 0x" << std::hex << PIN_GetContextReg(ctx, getHighReg(reg2)) << ")";
        break;
    }
  }
    
  symbolicElement *elem = new symbolicElement(dst, src, uniqueID);
  symbolicList.push_front(elem);
  symbolicReg[reg1_ID] = uniqueID++;

  if (taintedReg[reg2_ID] == TAINTED)
    taintedReg[reg1_ID] = TAINTED;
  else
    taintedReg[reg1_ID] = !TAINTED;

  elem->isTainted = taintedReg[reg1_ID];  

  if (elem->isTainted)
    taint << "#" << symbolicReg[reg1_ID] << " is controllable";

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % (*elem->symExpr).str() % taint.str();

  return;
}


VOID movRegImm(std::string insDis, ADDRINT insAddr, REG reg1, UINT64 imm, INT32 opcode)
{
  if (_analysisStatus == LOCKED)
    return;

  std::stringstream src, dst, taint;

  UINT64 reg1_ID = translatePinRegToID(reg1);

  dst << "#" << std::dec << uniqueID;
  src << "0x" << std::hex << imm;
    
  symbolicElement *elem = new symbolicElement(dst, src, uniqueID);
  symbolicList.push_front(elem);
  symbolicReg[reg1_ID] = uniqueID++;

  taintedReg[reg1_ID] = !TAINTED;

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % (*elem->symExpr).str() % taint.str();

  return;
}


VOID movRegMem(std::string insDis, ADDRINT insAddr, REG reg1, UINT64 mem, UINT32 readSize, INT32 opcode)
{
  if (_analysisStatus == LOCKED)
    return;

  std::list<UINT64>::iterator i;
  std::stringstream src, dst, taint;

  UINT64 reg1_ID  = translatePinRegToID(reg1);
  UINT64 size     = (REG_Size(reg1) * 8) - (readSize * 8);

  dst << "#" << std::dec << uniqueID;

  if (isMemoryReference(mem) != -1){
    switch(opcode){
      case XED_ICLASS_MOV:
        src << "#" << std::dec << isMemoryReference(mem);
        break;
      case XED_ICLASS_MOVSX:
        src << "SignExt(" << std::dec << size << ", #" << std::dec << isMemoryReference(mem) << ")";
        break;
      case XED_ICLASS_MOVZX:
        src << "ZeroExt(" << std::dec << size << ", #" << std::dec << isMemoryReference(mem) << ")";
        break;
    }
  }
  else{

    if (isMemoryTainted(mem) == TAINTED){
      switch(opcode){
        case XED_ICLASS_MOV:
          src << "SymVar_" << std::dec << numberOfSymVar++;
          break;
        case XED_ICLASS_MOVSX:
          src << "SignExt(" << std::dec << size << ", " << "SymVar_" << std::dec << numberOfSymVar++ << ")";
          break;
        case XED_ICLASS_MOVZX:
          src << "ZeroExt(" << std::dec << size << ", " << "SymVar_" << std::dec << numberOfSymVar++ << ")";
          break;
      } 
    }
    else {
      switch(readSize){
        case 1:
          switch(opcode){
            case XED_ICLASS_MOV:
              src << "0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT8 *>(mem)));
              break;
            case XED_ICLASS_MOVSX:
              src << "SignExt(" << std::dec << size << ", 0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT8 *>(mem))) << ")";
              break;
            case XED_ICLASS_MOVZX:
              src << "ZeroExt(" << std::dec << size << ", 0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT8 *>(mem))) << ")";
              break;
          }
          break;
        case 2:
          switch(opcode){
            case XED_ICLASS_MOV:
              src << "0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT16 *>(mem)));
              break;
            case XED_ICLASS_MOVSX:
              src << "SignExt(" << std::dec << size << ", 0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT16 *>(mem))) << ")";
              break;
            case XED_ICLASS_MOVZX:
              src << "ZeroExt(" << std::dec << size << ", 0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT16 *>(mem))) << ")";
              break;
          }
          break;
        case 4:
          switch(opcode){
            case XED_ICLASS_MOV:
              src << "0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT32 *>(mem)));
              break;
            case XED_ICLASS_MOVSX:
              src << "SignExt(" << std::dec << size << ", 0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT32 *>(mem))) << ")";
              break;
            case XED_ICLASS_MOVZX:
              src << "ZeroExt(" << std::dec << size << ", 0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT32 *>(mem))) << ")";
              break;
          }
          break;
        case 8:
          switch(opcode){
            case XED_ICLASS_MOV:
              src << "0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT64 *>(mem)));
              break;
            case XED_ICLASS_MOVSX:
              src << "SignExt(" << std::dec << size << ", 0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT64 *>(mem))) << ")";
              break;
            case XED_ICLASS_MOVZX:
              src << "ZeroExt(" << std::dec << size << ", 0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT64 *>(mem))) << ")";
              break;
          }
          break;
      }
    }
  }
    
  symbolicElement *elem = new symbolicElement(dst, src, uniqueID);
  symbolicList.push_front(elem);
  symbolicReg[reg1_ID]  = uniqueID++;
  taintedReg[reg1_ID]   = !TAINTED;
  elem->isTainted       = !TAINTED;

  /* Check if the source addr is tainted */
  if (isMemoryTainted(mem) == TAINTED){
      taintedReg[reg1_ID] = TAINTED;
      elem->isTainted     = TAINTED;
  }

  if (elem->isTainted)
    taint << "#" << symbolicReg[reg1_ID] << " is controllable";

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % (*elem->symExpr).str() % taint.str();

  return;
}


VOID movMemReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 writeSize, INT32 opcode)
{
  if (_analysisStatus == LOCKED)
    return;

  std::list<UINT64>::iterator i;
  std::stringstream src, dst, taint;

  UINT64 reg1_ID = translatePinRegToID(reg1);

  dst << "#" << std::dec << uniqueID;

  if (symbolicReg[reg1_ID] != (UINT64)-1)
    src << "#" << symbolicReg[reg1_ID];
  else 
    src << "0x" << std::hex << PIN_GetContextReg(ctx, getHighReg(reg1));

  symbolicElement *elem = new symbolicElement(dst, src, uniqueID);
  symbolicList.push_front(elem);
  elem->isTainted       = !TAINTED;

  /* If src reg is tainted, we taint the memory area */
  if (taintedReg[reg1_ID] == TAINTED){
    unsigned int offset = 0;
    for (; offset < writeSize ; offset++){
      if (isMemoryTainted(mem+offset) == 0)
        addressesTainted.push_front(mem+offset);
    }
    elem->isTainted = TAINTED;
  }

  /* If src reg is not tainted, we untaint the memory area */
  if (taintedReg[reg1_ID] != TAINTED){
    unsigned int offset = 0;
    for (; offset < writeSize ; offset++){
      addressesTainted.remove(mem+offset);
    }
    elem->isTainted = !TAINTED;
  }

  if (elem->isTainted)
    taint << "Memory area " << mem << " is controllable";

  /* Link the memory reference to the symbolic expression */
  memoryReference.push_front(make_pair(mem, uniqueID++));

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % (*elem->symExpr).str() % taint.str();

  return;
}


VOID movMemImm(std::string insDis, ADDRINT insAddr, UINT64 imm, UINT64 mem, UINT32 writeSize, INT32 opcode)
{
  if (_analysisStatus == LOCKED)
    return;

  std::list<UINT64>::iterator i;
  std::stringstream src, dst, taint;

  dst << "#" << std::dec << uniqueID;
  src << "0x" << std::hex << imm;

  symbolicElement *elem = new symbolicElement(dst, src, uniqueID);
  symbolicList.push_front(elem);
  elem->isTainted       = !TAINTED;

  /* We remove the taint if the memory area is tainted */
  unsigned int offset = 0;
  for (; offset < writeSize ; offset++){
    addressesTainted.remove(mem+offset);
  }

  /* Link the memory reference to the symbolic expression */
  memoryReference.push_front(make_pair(mem, uniqueID++));

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % (*elem->symExpr).str() % taint.str();

  return;
}

