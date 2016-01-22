//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>

#include <api.hpp>
#include <smt2lib.hpp>
#include <smt2libZ3Ast.hpp>
#include <smt2libZ3Result.hpp>
#include <solverEngine.hpp>



/*! \page solver_interface_page SMT Solver Interface
    \brief [**internal**] All information about the SMT solver interface.

\tableofcontents

\section solver_interface_description Description
<hr>

The solver engine is the interface between an SMT solver and **Triton** itself. All requests are sent to the SMT solver
as an \ref py_smt2lib_page AST. The AST representation as string looks like a manually crafted SMT2-LIB script.

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

The solver interface triton::API::getModel() gets as parameter a triton::smt2lib::smtAstAbstractNode which corresponds to the \f$ AST_{constraint} \f$ and
returns a list of triton::engines::solver::SolverModel. Each model for a symbolic variable \f$x \in X\f$ is represented by a triton::engines::solver::SolverModel.
For example, if there are two symbolic variables in your constraint, the triton::API::getModel() function will return a list of two items.

~~~~~~~~~~~~~{cpp}
  // Get the RAX's symbolic ID
  auto raxSymId = api.getSymbolicRegisterId(TRITON_X86_REG_RAX);

  // Get the RAX's full AST
  auto raxFullAst = api.getFullAstFromId(raxSymId);

  // Modify RAX's AST to build the constraint
  auto constraint = smt2lib::smtAssert(smt2lib::equal(raxFullAst, smt2lib::bv(0, raxFullAst->getBitvectorSize())));

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

      z3::expr mk_or(z3::expr_vector args) {
        std::vector<Z3_ast> array;

        for (triton::uint32 i = 0; i < args.size(); i++)
          array.push_back(args[i]);

        return to_expr(args.ctx(), Z3_mk_or(args.ctx(), array.size(), &(array[0])));
      }


      SolverEngine::SolverEngine() {
      }


      SolverEngine::~SolverEngine() {
      }


      std::list<std::map<triton::uint32, SolverModel>> SolverEngine::getModels(smt2lib::smtAstAbstractNode *node, triton::uint32 limit) {
        std::list<std::map<triton::uint32, SolverModel>>  ret;
        std::stringstream                                 formula;
        z3::context                                       ctx;
        z3::solver                                        solver(ctx);

        if (node == nullptr)
          throw std::runtime_error("SolverEngine::getModels(): node cannot be null.");

        /* First, set the QF_AUFBV flag  */
        formula << "(set-logic QF_AUFBV)";

        /* Then, delcare all symbolic variables */
        formula << triton::api.getVariablesDeclaration();

        /* And concat the user expression */
        formula << triton::api.getFullAst(node);

        /* Create the context and AST */
        Z3_ast ast = Z3_parse_smtlib2_string(ctx, formula.str().c_str(), 0, 0, 0, 0, 0, 0);
        z3::expr eq(ctx, ast);

        /* Create a solver and add the expression */
        solver.add(eq);

        /* Check if it is sat */
        while (solver.check() == z3::sat && limit >= 1) {

          /* Get model */
          z3::model m = solver.get_model();

          /* Traversing the model */
          std::map<triton::uint32, SolverModel> smodel;
          z3::expr_vector args(ctx);
          for (triton::uint32 i = 0; i < m.size(); i++) {

            z3::func_decl variable  = m[i];
            std::string varName     = variable.name().str();
            z3::expr exp            = m.get_const_interp(variable);
            triton::uint32 bvSize   = exp.get_sort().bv_size();
            std::string svalue      = Z3_get_numeral_string(ctx, exp);

            triton::uint512         value{svalue};
            SolverModel             trionModel{varName, value};
            smodel[trionModel.getId()] = trionModel;

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


      std::map<triton::uint32, SolverModel> SolverEngine::getModel(smt2lib::smtAstAbstractNode *node) {
        std::map<triton::uint32, SolverModel> ret;
        std::list<std::map<triton::uint32, SolverModel>> allModels;

        allModels = this->getModels(node, 1);
        if (allModels.size() > 0)
          ret = allModels.front();

        return ret;
      }


      triton::uint512 SolverEngine::evaluateAst(smt2lib::smtAstAbstractNode *node) {
        if (node == nullptr)
          throw std::runtime_error("SolverEngine::evaluateAst(): node cannot be null.");
        triton::smt2lib::Z3Ast z3ast{};
        triton::smt2lib::Z3Result result = z3ast.eval(*node);
        triton::uint512 nbResult{result.getStringValue()};
        return nbResult;
      }

    };
  };
};
