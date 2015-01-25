
#include "pin.H"
#include "triton.h"


static VOID setZF(UINT64 id)
{
  std::stringstream src, dst, taint;

  dst << "#" << std::dec << uniqueID;
  src << "(#" << std::dec << id << " == 0)";
    
  symbolicElement *elem = new symbolicElement(dst, src, uniqueID);
  symbolicList.push_front(elem);
  symbolicReg[ID_ZF] = uniqueID++;

  std::cout << boost::format(outputInstruction) % "" % "" % (*elem->symExpr).str() % taint.str();
}


VOID addRegImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 imm)
{
  if (_analysisStatus == LOCKED)
    return;

  std::stringstream src, dst, taint;

  UINT64 reg1_ID = translatePinRegToID(reg1);

  dst << "#" << std::dec << uniqueID;

  if (symbolicReg[reg1_ID] != (UINT64)-1)
    src << "(#" << std::dec << symbolicReg[reg1_ID] << " + 0x" << std::hex << imm << ")";
  else 
    src << "(0x" << std::hex << PIN_GetContextReg(ctx, getHighReg(reg1)) << " + 0x" << imm << ")";
    
  symbolicElement *elem = new symbolicElement(dst, src, uniqueID);
  symbolicList.push_front(elem);
  symbolicReg[reg1_ID] = uniqueID++;
  elem->isTainted = taintedReg[reg1_ID];

  if (elem->isTainted)
    taint << "#" << symbolicReg[reg1_ID] << " is controllable";

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % (*elem->symExpr).str() % taint.str();

  setZF(uniqueID - 1);

  return;
}


VOID addRegReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, REG reg2)
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

  src << "(" << vr1.str() << " + " << vr2.str() << ")";

  symbolicElement *elem = new symbolicElement(dst, src, uniqueID);
  symbolicList.push_front(elem);
  symbolicReg[reg1_ID] = uniqueID++;

  if (taintedReg[reg2_ID] == TAINTED)
    taintedReg[reg1_ID] = TAINTED;

  elem->isTainted = taintedReg[reg1_ID];  

  if (elem->isTainted)
    taint << "#" << symbolicReg[reg1_ID] << " is controllable";

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % (*elem->symExpr).str() % taint.str();

  setZF(uniqueID - 1);

  return;
}

