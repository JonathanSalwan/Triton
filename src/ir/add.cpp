
#include "pin.H"
#include "Triton.h"


/*
 * TODO :
 *
 * reg, imm <- done
 * reg, reg <- done
 *
 * mem, imm <- todo
 * mem, reg <- todo
 * reg, mem <- todo
 *
 * ZF <- done
 *
 * OF <- todo
 * SF <- todo
 * AF <- todo
 * CF <- todo
 * PF <- todo
 *
 * */

static VOID setZF(UINT64 id)
{
  std::stringstream expr;

  expr << "(assert (= #" << std::dec << id << " 0))";
    
  symbolicElement *elem = symbolicEngine->newSymbolicElement(expr);
  symbolicEngine->symbolicReg[ID_ZF] = elem->getID();

  std::cout << boost::format(outputInstruction) % "" % "" % elem->getExpression() % "";
}


VOID addRegImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 imm)
{
  if (_analysisStatus == LOCKED)
    return;

  std::stringstream expr, taint;

  UINT64 reg1_ID = translatePinRegToID(reg1);

  if (symbolicEngine->symbolicReg[reg1_ID] != (UINT64)-1)
    expr << "(+ #" << std::dec << symbolicEngine->symbolicReg[reg1_ID] << " " << smt2lib_bv(imm, REG_Size(reg1)) << ")";
  else 
    expr << "(+ " << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg1)), REG_Size(reg1)) << " " << smt2lib_bv(imm, REG_Size(reg1)) << ")";
    
  symbolicElement *elem = symbolicEngine->newSymbolicElement(expr);
  symbolicEngine->symbolicReg[reg1_ID] = elem->getID();
  elem->isTainted = taintEngine->getRegStatus(reg1_ID);

  if (elem->isTainted)
    taint << "#" << symbolicEngine->symbolicReg[reg1_ID] << " is controllable";

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % elem->getExpression() % taint.str();

  setZF(elem->getID());

  return;
}


VOID addRegReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, REG reg2)
{
  if (_analysisStatus == LOCKED)
    return;

  std::stringstream expr, vr1, vr2, taint;

  UINT64 reg1_ID = translatePinRegToID(reg1);
  UINT64 reg2_ID = translatePinRegToID(reg2);

  if (symbolicEngine->symbolicReg[reg1_ID] != (UINT64)-1)
    vr1 << "#" << std::dec << symbolicEngine->symbolicReg[reg1_ID];
  else
    vr1 << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg1)), REG_Size(reg1));
    
  if (symbolicEngine->symbolicReg[reg2_ID] != (UINT64)-1)
    vr2 << "#" << std::dec << symbolicEngine->symbolicReg[reg2_ID];
  else
    vr2 << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg2)), REG_Size(reg1));

  expr << "(+ " << vr1.str() << " " << vr2.str() << ")";

  symbolicElement *elem = symbolicEngine->newSymbolicElement(expr);
  symbolicEngine->symbolicReg[reg1_ID] = elem->getID();

  if (taintEngine->isRegTainted(reg2_ID))
    taintEngine->taintReg(reg1_ID);

  elem->isTainted = taintEngine->getRegStatus(reg1_ID);

  if (elem->isTainted)
    taint << "#" << symbolicEngine->symbolicReg[reg1_ID] << " is controllable";

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % elem->getExpression() % taint.str();

  setZF(elem->getID());

  return;
}


