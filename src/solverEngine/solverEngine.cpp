/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <SMT2Lib.h>
#include <SolverEngine.h>



/* Thanks http://stackoverflow.com/questions/10819875 */
namespace TritonSolver {

  z3::expr mk_or(z3::expr_vector args)
  {
    std::vector<Z3_ast> array;

    for (uint32 i = 0; i < args.size(); i++)
      array.push_back(args[i]);

    return to_expr(args.ctx(), Z3_mk_or(args.ctx(), array.size(), &(array[0])));
  }

}


SolverEngine::SolverEngine(SymbolicEngine *symEngine)
{
  this->symEngine = symEngine;
}


SolverEngine::~SolverEngine()
{
}


std::vector<std::list<Smodel>> SolverEngine::getModels(smt2lib::smtAstAbstractNode *node, uint64 limit)
{
  std::vector<std::list<Smodel>>  ret;
  std::stringstream               formula;
  z3::context                     *ctx;
  z3::solver                      *solver;

  /* First, set the QF_AUFBV flag  */
  formula << "(set-logic QF_AUFBV)";

  /* Then, delcare all symbolic variables */
  formula << this->symEngine->getVariablesDeclaration();

  /* And concat the user expression */
  formula << node;

  /* Create the context and AST */
  ctx = new z3::context();
  Z3_ast ast = Z3_parse_smtlib2_string(*ctx, formula.str().c_str(), 0, 0, 0, 0, 0, 0);
  z3::expr eq(*ctx, ast);

  /* Create a solver and add the expression */
  solver = new z3::solver(*ctx);
  solver->add(eq);

  /* Check if it is sat */
  while (solver->check() == z3::sat && limit >= 1){

    /* Get model */
    z3::model m = solver->get_model();

    /* Traversing the model */
    std::list<Smodel> smodel;
    z3::expr_vector args(*ctx);
    for (uint32 i = 0; i < m.size(); i++) {

      uint64        value     = 0;
      z3::func_decl variable  = m[i];
      std::string   varName   = variable.name().str();
      z3::expr      exp       = m.get_const_interp(variable);
      uint64        bvSize    = exp.get_sort().bv_size();

      /* Create a Triton Model */
      Z3_get_numeral_uint64(*ctx, exp, &value);
      smodel.push_back(Smodel(varName, value));

      if (exp.get_sort().is_bv())
        args.push_back(ctx->bv_const(varName.c_str(), bvSize) != ctx->bv_val(value, bvSize));

    }

    /* Escape last models */
    solver->add(TritonSolver::mk_or(args));

    /* If there is model available */
    if (smodel.size() > 0)
      ret.push_back(smodel);

    /* Decrement the limit */
    limit--;
  }

  delete solver;
  return ret;
}


std::list<Smodel> SolverEngine::getModel(smt2lib::smtAstAbstractNode *node)
{
  std::list<Smodel> ret;
  std::vector<std::list<Smodel>> allModels;

  allModels = this->getModels(node, 1);
  if (allModels.size() > 0)
    ret = allModels[0];

  return ret;
}

