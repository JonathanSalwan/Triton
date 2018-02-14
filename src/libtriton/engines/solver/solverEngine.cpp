//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <z3++.h>                        // for expr, model, solver, expr_ve...
#include <z3_api.h>                      // for Z3_ast, _Z3_ast
#include <iosfwd>                        // for ostringstream
#include <string>                        // for string
#include <triton/astContext.hpp>         // for AstContext
#include <triton/exceptions.hpp>         // for SolverEngine
#include <triton/solverEngine.hpp>       // for SolverEngine
#include <triton/solverModel.hpp>        // for SolverModel
#include <triton/tritonToZ3Ast.hpp>      // for TritonToZ3Ast
#include <triton/tritonTypes.hpp>        // for uint32, uint512


/*! \page solver_interface_page SMT Solver Interface
    \brief [**internal**] All information about the SMT solver interface.

\tableofcontents

\section solver_interface_description Description
<hr>

The solver engine is the interface between an SMT solver and **Triton** itself. All requests are sent to the SMT solver
as Triton AST (See: \ref py_AstContext_page). The AST representation as string looks like a manually crafted SMT2-LIB script.

<b>Example:</b>

~~~~~~~~~~~~~
; Declaration of the theory
(set-logic QF_AUFBV)

; Utility function
(define-fun parity ((x!1 (_ BitVec 8))) (_ BitVec 1)
  ; x ^= x >> 4;
  ; v &= 0xf;
  ; return (0x6996 >> v) & 1;

  ((_ extract 0 0)
    (bvlshr
       (_ bv27030 16)
       ((_ zero_extend 8)
        (bvand
          (bvxor
            x!1
            (bvlshr x!1 (_ bv4 8)))
          (_ bv15 8)))))
)

; Declaration of the free variables
(declare-fun SymVar_0 () (_ BitVec 8))

; Formula
(assert (= (ite ...)))
~~~~~~~~~~~~~

\section solver_interface_examples C++ example
<hr>

Let assume that the \f$rax\f$'s symbolic expression contains a symbolic variable \f$x_0 \in X\f$ which has been instantiated previously. At
this program point, we want that \f$rax = 0\f$. We first get the symbolic expression id corresponding to the \f$rax\f$ register, then, its AST.
When the AST has been got, we are able to build our constraint such that \f$ AST_{constraint} = assert(AST_{rax} == 0) \f$.

The solver interface triton::API::getModel() gets as parameter a triton::ast::AbstractNode which corresponds to the \f$ AST_{constraint} \f$ and
returns a list of triton::engines::solver::SolverModel. Each model for a symbolic variable \f$x \in X\f$ is represented by a triton::engines::solver::SolverModel.
For example, if there are two symbolic variables in your constraint, the triton::API::getModel() function will return a list of two items.

~~~~~~~~~~~~~{cpp}
// Get the symbolic id of RAX
auto raxSymId = api.getSymbolicRegisterId(TRITON_X86_REG_RAX);

// Get the full AST of RAX
auto raxFullAst = api.unrollAstFromId(raxSymId);

// Modify the AST of RAX to build the constraint
auto constraint = triton::ast::equal(raxFullAst, triton::ast::bv(0, raxFullAst->getBitvectorSize()));

// Ask a model
auto model = api.getModel(constraint);

// Display all symbolic variable value contained in the model
std::cout << "Model:" << std::endl;
for (auto it = model.begin(); it != model.end(); it++) {
  std::cout << "  - Variable: " << it->getName() << std::endl;
  std::cout << "  - Value   : " << std::hex << it->getValue() << std::endl;
}
~~~~~~~~~~~~~

*/



namespace triton {
  namespace engines {
    namespace solver {

      //! Wrapper to handle variadict number of arguments or'd togethers
      // FIXME : It is already implemented in the new Z3 interface.
      z3::expr mk_or(z3::expr_vector args) {
        std::vector<Z3_ast> array;

        for (triton::uint32 i = 0; i < args.size(); i++)
          array.push_back(args[i]);

        return to_expr(args.ctx(), Z3_mk_or(args.ctx(), static_cast<triton::uint32>(array.size()), &(array[0])));
      }


      SolverEngine::SolverEngine(triton::engines::symbolic::SymbolicEngine* symbolicEngine) {
        if (symbolicEngine == nullptr)
          throw triton::exceptions::SolverEngine("SolverEngine::SolverEngine(): The symbolicEngine API cannot be null.");
        this->symbolicEngine = symbolicEngine;
      }


      SolverEngine::SolverEngine(const SolverEngine& other) {
        this->symbolicEngine = other.symbolicEngine;
      }


      SolverEngine& SolverEngine::operator=(const SolverEngine& other) {
        this->symbolicEngine = other.symbolicEngine;
        return *this;
      }


      std::list<std::map<triton::uint32, SolverModel>> SolverEngine::getModels(triton::ast::AbstractNode* node, triton::uint32 limit) const {
        std::list<std::map<triton::uint32, SolverModel>> ret;
        triton::ast::TritonToZ3Ast z3Ast{this->symbolicEngine, false};

        z3::expr      expr = z3Ast.convert(node);
        z3::context&  ctx  = expr.ctx();
        z3::solver    solver(ctx);

        if (node == nullptr)
          throw triton::exceptions::SolverEngine("SolverEngine::getModels(): node cannot be null.");

        if (node->isLogical() == false)
          throw triton::exceptions::SolverEngine("SolverEngine::getModels(): Must be a logical node.");

        /* Create a solver and add the expression */
        solver.add(expr);

        /* Check if it is sat */
        while (solver.check() == z3::sat && limit >= 1) {

          /* Get model */
          z3::model m = solver.get_model();

          /* Traversing the model */
          std::map<triton::uint32, SolverModel> smodel;
          z3::expr_vector args(ctx);
          for (triton::uint32 i = 0; i < m.size(); i++) {

            /* Get the z3 variable */
            z3::func_decl z3Variable = m[i];

            /* Get the name as std::string from a z3 variable */
            std::string varName = z3Variable.name().str();

            /* Get z3 expr */
            z3::expr exp = m.get_const_interp(z3Variable);

            /* Get the size of a z3 expr */
            triton::uint32 bvSize = exp.get_sort().bv_size();

            /* Get the value of a z3 expr */
            std::string svalue = Z3_get_numeral_string(ctx, exp);

            /* Convert a string value to a integer value */
            triton::uint512 value = triton::uint512(svalue);

            /* Create a triton model */
            SolverModel trionModel = SolverModel(varName, value);

            /* Map the result */
            smodel[trionModel.getId()] = trionModel;

            /* Uniq result */
            if (exp.get_sort().is_bv())
              args.push_back(ctx.bv_const(varName.c_str(), bvSize) != ctx.bv_val(svalue.c_str(), bvSize));

          }

          /* Escape last models */
          solver.add(triton::engines::solver::mk_or(args));

          /* If there is model available */
          if (smodel.size() > 0)
            ret.push_back(smodel);

          /* Decrement the limit */
          limit--;
        }

        return ret;
      }


      std::map<triton::uint32, SolverModel> SolverEngine::getModel(triton::ast::AbstractNode* node) const {
        std::map<triton::uint32, SolverModel> ret;
        std::list<std::map<triton::uint32, SolverModel>> allModels;

        allModels = this->getModels(node, 1);
        if (allModels.size() > 0)
          ret = allModels.front();

        return ret;
      }

    };
  };
};
