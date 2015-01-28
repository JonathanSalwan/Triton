
#include "SolverEngine.h"


/* Replace a symbolic element ID by its source expression */
static std::string replaceEq(std::string str, const std::string from, const std::string to)
{
  size_t start_pos = str.find(from);
  if(start_pos == std::string::npos)
      return NULL;
  str.replace(start_pos, from.length(), to);
  return str;
}


/* Reconstructs all symbolic elements ID */
static std::string formulaReconstruction(SymbolicEngine *symbolicEngine, uint64_t id)
{
  int value;
  std::size_t found;
  std::stringstream formula;

  std::stringstream from;
  std::stringstream to;

  formula.str(symbolicEngine->getElementFromId(id)->getSource());
  while (formula.str().find("#") != std::string::npos){

    from.str("");
    to.str("");

    found = formula.str().find("#") + 1;
    std::string subs = formula.str().substr(found, std::string::npos);
    value = atoi(subs.c_str());
    from << "#" << value;
    to.str(symbolicEngine->getElementFromId(value)->getSource());

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


/* Solve a formula based on the symbolic element ID */
void SolverEngine::solveFromID(uint64_t id)
{
  std::stringstream formula;

  /* Reconstruct the full formula by backward analysis */
  formula.str(formulaReconstruction(symEngine, this->symEngine->symbolicReg[ID_ZF]));

  /* First, set the QF_AUFBV flag */
  this->formula << "(set-logic QF_AUFBV)";

  /* Then, delcare all symbolic variables */
  this->formula << this->symEngine->getSmt2LibVarsDecl();

  /* And concat the formula */
  this->formula << formula.str();

  this->ctx = new z3::context();

  Z3_ast ast = Z3_parse_smtlib2_string(*this->ctx, this->formula.str().c_str(), 0, 0, 0, 0, 0, 0);
  z3::expr eq(*this->ctx, ast);
  this->solver = new z3::solver(*this->ctx);
  this->solver->add(eq);
  this->checkResult = this->solver->check();
}


/* Hard display the current model */
void SolverEngine::displayModel()
{
  std::cout << "----- Model -----" << std::endl;
  if (this->checkResult == z3::sat){
    z3::model m = this->solver->get_model();
    std::cout << m << std::endl;
  }
  else {
    std::cout << "__UNSAT__";
  }
  std::cout << "-----------------" << std::endl;
}


/* Returns the current model */
z3::model SolverEngine::getModel()
{
  return this->solver->get_model();
}


/* Returns the result's status of the current model */
z3::check_result SolverEngine::getCheckResult()
{
  return this->checkResult;
}


/* Returns the full symbolic formula */
std::string SolverEngine::getFormula()
{
  return this->formula.str();
}

