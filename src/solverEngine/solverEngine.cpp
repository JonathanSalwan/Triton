
#include <Colors.h>
#include <SMT2Lib.h>
#include <SolverEngine.h>


SolverEngine::SolverEngine(SymbolicEngine *symEngine)
{
  this->symEngine = symEngine;
}


SolverEngine::~SolverEngine()
{
}


std::list< std::pair<std::string, unsigned long long> > SolverEngine::getModel(std::string expr)
{
  std::list< std::pair<std::string, unsigned long long> > ret;
  std::stringstream   formula;
  z3::check_result    checkResult;
  z3::context         *ctx;
  z3::solver          *solver;

  /* First, set the QF_AUFBV flag */
  formula << smt2lib::init();

  /* Then, delcare all symbolic variables */
  formula << this->symEngine->getVariablesDeclaration();

  /* And concat the user expression */
  formula << expr;

  /* Create the context and AST */
  ctx = new z3::context();
  Z3_ast ast = Z3_parse_smtlib2_string(*ctx, formula.str().c_str(), 0, 0, 0, 0, 0, 0);
  z3::expr eq(*ctx, ast);

  /* Create a solver and add the expression */
  solver = new z3::solver(*ctx);
  solver->add(eq);

  /* Check */
  checkResult = solver->check();

  /* Check if it is sat */
  if (checkResult == z3::sat){
    /* Get model */
    z3::model m = solver->get_model();
    /* Traversing the model */
    for (unsigned i = 0; i < m.size(); i++) {
      unsigned long long value = 0;
      z3::func_decl v = m[i];
      Z3_get_numeral_uint64(*ctx, m.get_const_interp(v), &value);
      ret.push_back(make_pair(v.name().str(), value));
    }
  }

  delete solver;
  return ret;
}

