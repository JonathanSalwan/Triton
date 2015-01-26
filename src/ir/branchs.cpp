
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


VOID solveFormula(std::string formula)
{
  z3::context ctx;

  Z3_ast ast = Z3_parse_smtlib2_string(ctx, formula.c_str(), 0, 0, 0, 0, 0, 0);
  z3::expr eq(ctx, ast);
  z3::solver s(ctx);

  s.add(eq);
  s.check();

  z3::model m = s.get_model();

  std::cout << "----- Model -----" << std::endl << m << std::endl << "-----------------" << std::endl;
}


VOID branchs(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT32 opcode)
{
  if (_analysisStatus == LOCKED)
    return;

  std::list<std::string>::iterator i;
  std::stringstream formula;
  std::stringstream stream;

  formula.str(formulaReconstruction(symbolicReg[ID_ZF]));

  for(i = smt2libVarDeclList.begin(); i != smt2libVarDeclList.end(); i++)
    stream << *i;
  stream << formula.str();

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % stream.str() % "";

  solveFormula(stream.str());
}


