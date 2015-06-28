
#include <SMT2Lib.h>
#include <SolverEngine.h>


SolverEngine::SolverEngine(SymbolicEngine *symEngine)
{
  this->symEngine = symEngine;
}


SolverEngine::~SolverEngine()
{
}


std::list<Smodel> SolverEngine::getModel(std::string expr)
{
  std::list<Smodel>   ret;
  std::stringstream   formula;
  z3::context         *ctx;
  z3::solver          *solver;

  /* First, set the QF_AUFBV flag and add global declarations */
  formula << smt2lib::logic();
  formula << smt2lib::global();

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

  /* Check if it is sat */
  if (solver->check() == z3::sat){
    /* Get model */
    z3::model m = solver->get_model();
    /* Traversing the model */
    for (uint32 i = 0; i < m.size(); i++) {
      uint64 value = 0;
      z3::func_decl v = m[i];
      Z3_get_numeral_uint64(*ctx, m.get_const_interp(v), &value);
      ret.push_back(Smodel(v.name().str(), value));
    }
  }

  delete solver;
  return ret;
}

