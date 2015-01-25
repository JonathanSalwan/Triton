
#include "pin.H"
#include "triton.h"



static VOID setMem(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 readSize)
{
  std::list<UINT64>::iterator i;
  std::stringstream src, dst, taint;

  UINT64 reg1_ID = translatePinRegToID(reg1);

  dst << "#" << std::dec << uniqueID;

  if (isMemoryReference(mem) != -1){
    src << "#" << std::dec << isMemoryReference(mem);
  }
  else{
    switch(readSize){
      case 1:
        src << "0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT8 *>(mem)));
        break;
      case 2:
        src << "0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT16 *>(mem)));
        break;
      case 4:
        src << "0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT32 *>(mem)));
        break;
      case 8:
        src << "0x" << std::hex << static_cast<UINT64>(*(reinterpret_cast<UINT64 *>(mem)));
        break;
    }
  }
    
  symbolicElement *elem = new symbolicElement(dst, src, uniqueID);
  symbolicList.push_front(elem);
  symbolicReg[reg1_ID]  = uniqueID++;
  taintedReg[reg1_ID]   = !TAINTED;
  elem->isTainted       = !TAINTED;

  /* Check if the source addr is tainted */
  for(i = addressesTainted.begin(); i != addressesTainted.end(); i++){
    if ( (mem >= *i) && (mem+(readSize-1)) <= *i){
      taintedReg[reg1_ID] = TAINTED;
      elem->isTainted     = TAINTED;
      break;
    }
  }

  if (elem->isTainted)
    taint << "#" << symbolicReg[reg1_ID] << " is controllable";

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % (*elem->symExpr).str() % taint.str();
}


static VOID alignStack(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT64 mem)
{
  std::stringstream src, dst, taint;

  /* Sub RSP */
  dst << "#" << std::dec << uniqueID;

  if (symbolicReg[ID_RSP] != (UINT64)-1)
    src << "#" << std::dec << symbolicReg[ID_RSP] << " + 8";
  else
    src << "0x" << std::hex << PIN_GetContextReg(ctx, REG_RSP) << " + 8";

  symbolicElement *elem = new symbolicElement(dst, src, uniqueID);
  symbolicList.push_front(elem);
  symbolicReg[ID_RSP] = uniqueID;

  /* Memory reference */
  memoryReference.push_front(make_pair(mem, uniqueID++));

  std::cout << boost::format(outputInstruction) % "" % "" % (*elem->symExpr).str() % taint.str();

  return;
}


VOID popReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 readSize)
{
  if (_analysisStatus == LOCKED)
    return;

  setMem(insDis, insAddr, ctx, reg1, mem, readSize);
  alignStack(insDis, insAddr, ctx, mem);

  return;
}

