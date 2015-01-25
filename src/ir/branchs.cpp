
#include "pin.H"
#include "triton.h"



std::stringstream *getEqById(UINT64 id)
{
  std::list<symbolicElement *>::iterator i;

  for(i = symbolicList.begin(); i != symbolicList.end(); i++){
    if ((*i)->uniqueID == id)
      return (*i)->symSrc;
  }
  return NULL;
}


std::string replaceEq(std::string str, const std::string from, const std::string to)
{
  size_t start_pos = str.find(from);
  if(start_pos == std::string::npos)
      return NULL;
  str.replace(start_pos, from.length(), to);
  return str;
}


std::string formulaReconstruction(UINT64 id)
{
  int value;
  std::size_t found;
  std::stringstream formula;

  std::stringstream from;
  std::stringstream to;

  formula.str(getEqById(id)->str());

  while (formula.str().find("#") != std::string::npos){

    found = formula.str().find("#") + 1;
    std::string subs = formula.str().substr(found, std::string::npos);

    value = atoi(subs.c_str());

    from << "#" << value;
    to << getEqById(value)->str();

    formula.str(replaceEq(formula.str(), from.str(), to.str()));
  }
  
  return formula.str();
}


VOID branchs(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT32 opcode)
{
  if (_analysisStatus == LOCKED)
    return;

  std::stringstream info;
  std::stringstream formula;

  info << "Branch: ZF #" <<  symbolicReg[ID_ZF];

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % info.str() % "";

  formula.str(formulaReconstruction(symbolicReg[ID_ZF]));

  std::cout << boost::format(outputInstruction) % "" % "" % formula.str() % "";
}


