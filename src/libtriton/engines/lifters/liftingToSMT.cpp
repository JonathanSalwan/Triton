//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <algorithm>
#include <map>
#include <vector>

#include <triton/astEnums.hpp>
#include <triton/liftingToSMT.hpp>
#include <triton/tritonTypes.hpp>



namespace triton {
  namespace engines {
    namespace lifters {

      LiftingToSMT::LiftingToSMT(const triton::ast::SharedAstContext& astCtxt, triton::engines::symbolic::SymbolicEngine* symbolic)
        : astCtxt(astCtxt), symbolic(symbolic) {
      }


      std::ostream& LiftingToSMT::liftToSMT(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr, bool assert_) {
        /* Save the AST representation mode */
        triton::ast::representations::mode_e mode = this->astCtxt->getRepresentationMode();
        this->astCtxt->setRepresentationMode(triton::ast::representations::SMT_REPRESENTATION);

        /* Collect SSA form */
        auto ssa = this->symbolic->sliceExpressions(expr);
        std::vector<triton::usize> symExprs;
        for (const auto& se : ssa) {
          symExprs.push_back(se.first);
        }

        /* Collect used symbolic variables */
        std::map<triton::usize, triton::engines::symbolic::SharedSymbolicVariable> symVars;
        for (const auto& n : triton::ast::search(expr->getAst(), triton::ast::VARIABLE_NODE)) {
          auto var = reinterpret_cast<triton::ast::VariableNode*>(n.get())->getSymbolicVariable();
          symVars[var->getId()] = var;
        }

        /* Print symbolic variables */
        for (const auto& var : symVars) {
          auto n = this->astCtxt->declare(this->astCtxt->variable(var.second));
          this->astCtxt->print(stream, n.get());
          stream << std::endl;
        }

        /* Sort SSA */
        std::sort(symExprs.begin(), symExprs.end());
        if (assert_) {
          /* The last node will be handled later to separate conjuncts */
          symExprs.pop_back();
        }

        /* Print symbolic expressions */
        for (const auto& id : symExprs) {
          stream << ssa[id]->getFormattedExpression() << std::endl;
        }

        if (assert_) {
          /* Print conjuncts in separate asserts */
          std::vector<triton::ast::SharedAbstractNode> exprs;
          std::vector<triton::ast::SharedAbstractNode> wl{expr->getAst()};

          while (!wl.empty()) {
            auto n = wl.back();
            wl.pop_back();

            if (n->getType() != ast::LAND_NODE) {
              exprs.push_back(n);
              continue;
            }

            for (const auto& child : n->getChildren()) {
              wl.push_back(child);
            }
          }

          for (auto it = exprs.crbegin(); it != exprs.crend(); ++it) {
            this->astCtxt->print(stream, this->astCtxt->assert_(*it).get());
            stream << std::endl;
          }

          stream << "(check-sat)" << std::endl;
          stream << "(get-model)" << std::endl;
        }

        /* Restore the AST representation mode */
        this->astCtxt->setRepresentationMode(mode);

        return stream;
      }

    }; /* lifters namespace */
  }; /* engines namespace */
}; /* triton namespace */
