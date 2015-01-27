
#include "pin.H"
#include "Triton.h"


static std::string replaceEq(std::string str, const std::string from, const std::string to)
{
  size_t start_pos = str.find(from);
  if(start_pos == std::string::npos)
      return NULL;
  str.replace(start_pos, from.length(), to);
  return str;
}


static std::string formulaReconstruction(UINT64 id)
{
  int value;
  std::size_t found;
  std::stringstream formula;

  std::stringstream from;
  std::stringstream to;

  formula.str(symbolicEngine->getElementFromId(id)->getSource());


  while (formula.str().find("#") != std::string::npos){

    found = formula.str().find("#") + 1;
    std::string subs = formula.str().substr(found, std::string::npos);

    value = atoi(subs.c_str());

    from << "#" << value;
    to << symbolicEngine->getElementFromId(value)->getSource();
  
    formula.str(replaceEq(formula.str(), from.str(), to.str()));
  }
  
  return formula.str();
}


SolverEngine::SolverEngine(SymbolicEngine *symEngine)
{
  this->symEngine = symEngine;
}


SolverEngine::~SolverEngine()
{
}


VOID SolverEngine::solveFromID(UINT64 id)
{
  std::stringstream formula;

  formula.str(formulaReconstruction(symEngine->symbolicReg[ID_ZF]));

  this->formula << this->symEngine->getSmt2LibVarsDecl();
  this->formula << formula.str();

  this->ctx = new z3::context();

  Z3_ast ast = Z3_parse_smtlib2_string(*this->ctx, this->formula.str().c_str(), 0, 0, 0, 0, 0, 0);
  z3::expr eq(*this->ctx, ast);
  this->solver = new z3::solver(*this->ctx);
  this->solver->add(eq);
  this->solver->check();
}


VOID SolverEngine::displayModel()
{
  z3::model m = this->solver->get_model();
  std::cout << "----- Model -----" << std::endl << m << std::endl << "-----------------" << std::endl;
}


z3::model SolverEngine::getModel()
{
  return this->solver->get_model();
}


std::string SolverEngine::getFormula()
{
  return this->formula.str();
}

