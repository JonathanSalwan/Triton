
#include "pin.H"
#include "dse.h"



VOID cmpRegImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 imm)
{
  if (_analysisStatus == LOCKED)
    return;

  std::stringstream src, dst, taint;

  UINT64 reg1_ID = translatePinRegToID(reg1);

  dst << "#" << std::dec << uniqueID;

  if (symbolicReg[reg1_ID] != (UINT64)-1)
    src << "(#" << std::dec << symbolicReg[reg1_ID] << " == 0x" << std::hex << imm << " ? 1, 0)";
  else 
    src << "(0x" << std::hex << PIN_GetContextReg(ctx, getHighReg(reg1)) << " == 0x" << imm << " ? 1, 0)";
    
  symbolicElement *elem = new symbolicElement(dst, src, uniqueID);
  symbolicList.push_front(elem);
  symbolicReg[ID_ZF] = uniqueID++;

  if (symbolicReg[reg1_ID] != (UINT64)-1 && taintedReg[reg1_ID] == TAINTED)
    taint << "#" << std::dec << symbolicReg[reg1_ID] << " is controllable";

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % (*elem->symExpr).str() % taint.str();

  return;
}


VOID cmpRegReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, REG reg2)
{
  if (_analysisStatus == LOCKED)
    return;

  std::stringstream src, dst, vr1, vr2, taint;

  UINT64 reg1_ID = translatePinRegToID(reg1);
  UINT64 reg2_ID = translatePinRegToID(reg2);

  dst << "#" << std::dec << uniqueID;

  if (symbolicReg[reg1_ID] != (UINT64)-1)
    vr1 << "#" << std::dec << symbolicReg[reg1_ID];
  else
    vr1 << "0x" << std::hex << PIN_GetContextReg(ctx, getHighReg(reg1));
    
  if (symbolicReg[reg2_ID] != (UINT64)-1)
    vr2 << "#" << std::dec << symbolicReg[reg2_ID];
  else
    vr2 << "0x" << std::hex << PIN_GetContextReg(ctx, getHighReg(reg2));

  src << "(" << vr1.str() << " == " << vr2.str() << ") ? 1, 0)";

  symbolicElement *elem = new symbolicElement(dst, src, uniqueID);
  symbolicList.push_front(elem);
  symbolicReg[ID_ZF] = uniqueID++;

  if (symbolicReg[reg1_ID] != (UINT64)-1 && taintedReg[reg1_ID] == TAINTED)
    taint << "#" << std::dec << symbolicReg[reg1_ID] << " is controllable";

  if (symbolicReg[reg2_ID] != (UINT64)-1 && taintedReg[reg2_ID] == TAINTED){
    if (!taint.str().empty())
      taint << " and ";
    taint << "#" << std::dec << symbolicReg[reg2_ID] << " is controllable";
  }

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % (*elem->symExpr).str() % taint.str();

  return;
}


VOID cmpMemImm(std::string insDis, ADDRINT insAddr, UINT64 imm, UINT64 mem, UINT32 readSize)
{
  if (_analysisStatus == LOCKED)
    return;

  std::stringstream src, dst, vr1, vr2, taint;

  dst << "#" << std::dec << uniqueID;

  if (isMemoryReference(mem) != -1){
    src << "(#" << std::dec << isMemoryReference(mem) << " == 0x" << std::hex << imm << ") ? 1, 0)";
  }
  else{
    switch(readSize){
      case 1:
        src << "(0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT8 *>(mem))) << " == " << std::hex << imm << ") ? 1, 0)";
        break;
      case 2:
        src << "(0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT16 *>(mem))) << " == " << std::hex << imm << ") ? 1, 0)";
        break;
      case 4:
        src << "(0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT32 *>(mem))) << " == " << std::hex << imm << ") ? 1, 0)";
        break;
      case 8:
        src << "(0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT64 *>(mem))) << " == " << std::hex << imm << ") ? 1, 0)";
        break;
    }
  }

  symbolicElement *elem = new symbolicElement(dst, src, uniqueID);
  symbolicList.push_front(elem);
  symbolicReg[ID_ZF] = uniqueID++;

  if (isMemoryTainted(mem) == TAINTED){
    if (isMemoryReference(mem) != -1){
      taint << "#" << std::dec << isMemoryReference(mem) << " is controllable";
    }
    else{
      switch(readSize){
        case 1:
          src << "0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT8 *>(mem))) << " is controllable";
          break;
        case 2:
          src << "0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT16 *>(mem))) << " is controllable";
          break;
        case 4:
          src << "0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT32 *>(mem))) << " is controllable";
          break;
        case 8:
          src << "0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT64 *>(mem))) << " is controllable";
          break;
      }
    }
  }

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % (*elem->symExpr).str() % taint.str();

  return ;
}


