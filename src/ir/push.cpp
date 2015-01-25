//
//  Jonathan Salwan - 2015-01-24
// 
//  http://shell-storm.org
//  http://twitter.com/JonathanSalwan
// 
//  This program is free software: you can redistribute it and/or modify
//  it under the terms of the GNU General Public License as published by
//  the Free Software  Foundation, either  version 3 of  the License, or
//  (at your option) any later version.
//

#include "pin.H"
#include "dse.h"



static VOID alignStack(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT64 mem)
{
  std::stringstream src, dst, taint;

  /* Sub RSP */
  dst << "#" << std::dec << uniqueID;

  if (symbolicReg[ID_RSP] != (UINT64)-1)
    src << "#" << std::dec << symbolicReg[ID_RSP] << " - 8";
  else
    src << "0x" << std::hex << PIN_GetContextReg(ctx, REG_RSP) << " - 8";

  symbolicElement *elem = new symbolicElement(dst, src, uniqueID);
  symbolicList.push_front(elem);
  symbolicReg[ID_RSP] = uniqueID;

  /* Memory reference */
  memoryReference.push_front(make_pair(mem, uniqueID++));

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % (*elem->symExpr).str() % taint.str();

  return;
}


static VOID setMemReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 writeSize)
{
  /* Push in memory */
  UINT64 reg1_ID = translatePinRegToID(reg1);

  std::stringstream src, dst, taint;

  dst << "#" << std::dec << uniqueID;

  if (symbolicReg[reg1_ID] != (UINT64)-1)
    src << "#" << std::dec << symbolicReg[reg1_ID];
  else
    src << "0x" << std::hex << PIN_GetContextReg(ctx, getHighReg(reg1));

  symbolicElement *elem = new symbolicElement(dst, src, uniqueID);
  symbolicList.push_front(elem);

  /* We remove the taint by default */
  unsigned int offset = 0;
  for (; offset < writeSize ; offset++){
    addressesTainted.remove(mem+offset);
  }

  /* Then, we taint if the reg is tainted */
  if (taintedReg[reg1_ID] == TAINTED){
    for (offset = 0; offset < writeSize ; offset++){
      addressesTainted.push_front(mem+offset);
    }
  }

  /* Memory reference */
  memoryReference.push_front(make_pair(mem, uniqueID++));

  std::cout << boost::format(outputInstruction) % "" % "" % (*elem->symExpr).str() % taint.str();
}


static VOID setMemImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT64 imm, UINT64 mem, UINT32 writeSize)
{
  std::stringstream src, dst, taint;

  dst << "#" << std::dec << uniqueID;
  src << "0x" << std::hex << imm;


  symbolicElement *elem = new symbolicElement(dst, src, uniqueID);
  symbolicList.push_front(elem);

  /* We remove the taint by default */
  unsigned int offset = 0;
  for (; offset < writeSize ; offset++){
    addressesTainted.remove(mem+offset);
  }

  /* Memory reference */
  memoryReference.push_front(make_pair(mem, uniqueID++));

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % (*elem->symExpr).str() % taint.str();

}


VOID pushReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 writeSize)
{
  if (_analysisStatus == LOCKED)
    return;

  alignStack(insDis, insAddr, ctx, mem);
  setMemReg(insDis, insAddr, ctx, reg1, mem, writeSize);

  return;
}


VOID pushImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT64 imm, UINT64 mem, UINT32 writeSize)
{
  if (_analysisStatus == LOCKED)
    return;
 
  alignStack(insDis, insAddr, ctx, mem);
  setMemImm(insDis, insAddr, ctx, imm, mem, writeSize);

  return;
}

