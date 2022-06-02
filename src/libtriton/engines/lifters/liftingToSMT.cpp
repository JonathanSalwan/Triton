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


      void LiftingToSMT::requiredFunctions(std::ostream& stream) {
        stream << "(define-fun bswap8 ((value (_ BitVec 8))) (_ BitVec 8)" << std::endl;
        stream << "    value" << std::endl;
        stream << ")" << std::endl;

        stream << std::endl;
        stream << "(define-fun bswap16 ((value (_ BitVec 16))) (_ BitVec 16)" << std::endl;
        stream << "  (bvor" << std::endl;
        stream << "    (bvshl" << std::endl;
        stream << "      (bvand value (_ bv255 16))" << std::endl;
        stream << "      (_ bv8 16)" << std::endl;
        stream << "    )" << std::endl;
        stream << "    (bvand (bvlshr value (_ bv8 16)) (_ bv255 16))" << std::endl;
        stream << "  )" << std::endl;
        stream << ")" << std::endl;

        stream << std::endl;
        stream << "(define-fun bswap32 ((value (_ BitVec 32))) (_ BitVec 32)" << std::endl;
        stream << "  (bvor" << std::endl;
        stream << "    (bvshl" << std::endl;
        stream << "      (bvor" << std::endl;
        stream << "        (bvshl" << std::endl;
        stream << "          (bvor" << std::endl;
        stream << "            (bvshl" << std::endl;
        stream << "              (bvand value (_ bv255 32))" << std::endl;
        stream << "              (_ bv8 32)" << std::endl;
        stream << "            )" << std::endl;
        stream << "            (bvand (bvlshr value (_ bv8 32)) (_ bv255 32))" << std::endl;
        stream << "          )" << std::endl;
        stream << "          (_ bv8 32)" << std::endl;
        stream << "        )" << std::endl;
        stream << "        (bvand (bvlshr value (_ bv16 32)) (_ bv255 32))" << std::endl;
        stream << "      )" << std::endl;
        stream << "      (_ bv8 32)" << std::endl;
        stream << "    )" << std::endl;
        stream << "    (bvand (bvlshr value (_ bv24 32)) (_ bv255 32))" << std::endl;
        stream << "  )" << std::endl;
        stream << ")" << std::endl;

        stream << std::endl;
        stream << "(define-fun bswap64 ((value (_ BitVec 64))) (_ BitVec 64)" << std::endl;
        stream << "  (bvor" << std::endl;
        stream << "    (bvshl" << std::endl;
        stream << "      (bvor" << std::endl;
        stream << "        (bvshl" << std::endl;
        stream << "          (bvor" << std::endl;
        stream << "            (bvshl" << std::endl;
        stream << "              (bvor" << std::endl;
        stream << "                (bvshl" << std::endl;
        stream << "                  (bvor" << std::endl;
        stream << "                    (bvshl" << std::endl;
        stream << "                      (bvor" << std::endl;
        stream << "                        (bvshl" << std::endl;
        stream << "                          (bvor" << std::endl;
        stream << "                            (bvshl" << std::endl;
        stream << "                              (bvand value (_ bv255 64))" << std::endl;
        stream << "                              (_ bv8 64)" << std::endl;
        stream << "                            )" << std::endl;
        stream << "                            (bvand (bvlshr value (_ bv8 64)) (_ bv255 64))" << std::endl;
        stream << "                          )" << std::endl;
        stream << "                          (_ bv8 64)" << std::endl;
        stream << "                        )" << std::endl;
        stream << "                        (bvand (bvlshr value (_ bv16 64)) (_ bv255 64))" << std::endl;
        stream << "                      )" << std::endl;
        stream << "                      (_ bv8 64)" << std::endl;
        stream << "                    )" << std::endl;
        stream << "                    (bvand (bvlshr value (_ bv24 64)) (_ bv255 64))" << std::endl;
        stream << "                  )" << std::endl;
        stream << "                  (_ bv8 64)" << std::endl;
        stream << "                )" << std::endl;
        stream << "                (bvand (bvlshr value (_ bv32 64)) (_ bv255 64))" << std::endl;
        stream << "              )" << std::endl;
        stream << "              (_ bv8 64)" << std::endl;
        stream << "            )" << std::endl;
        stream << "            (bvand (bvlshr value (_ bv40 64)) (_ bv255 64))" << std::endl;
        stream << "          )" << std::endl;
        stream << "          (_ bv8 64)" << std::endl;
        stream << "        )" << std::endl;
        stream << "        (bvand (bvlshr value (_ bv48 64)) (_ bv255 64))" << std::endl;
        stream << "      )" << std::endl;
        stream << "      (_ bv8 64)" << std::endl;
        stream << "    )" << std::endl;
        stream << "    (bvand (bvlshr value (_ bv56 64)) (_ bv255 64))" << std::endl;
        stream << "  )" << std::endl;
        stream << ")" << std::endl;

        stream << std::endl;
      }


      std::ostream& LiftingToSMT::liftToSMT(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr, bool assert_, bool icomment) {
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

        /* Print required functions */
        this->requiredFunctions(stream);

        /* Declare arrays if exist */
        for (const auto& array : triton::ast::search(expr->getAst(), triton::ast::ARRAY_NODE)) {
          auto n = this->astCtxt->declare(array);
          stream << n << std::endl;
        }

        /* Print symbolic variables */
        for (const auto& var : symVars) {
          auto n = this->astCtxt->declare(this->astCtxt->variable(var.second));
          stream << n << std::endl;
        }

        /* Sort SSA */
        std::sort(symExprs.begin(), symExprs.end());
        if (assert_) {
          /* The last node will be handled later to separate conjuncts */
          symExprs.pop_back();
        }

        /* Print symbolic expressions */
        for (const auto& id : symExprs) {
          auto& e = ssa[id];
          stream << e->getFormattedExpression();
          if (icomment && !e->getDisassembly().empty()) {
            if (e->getComment().empty()) {
              stream << " ; ";
            }
            else {
              stream << " - ";
            }
            stream << e->getDisassembly();
          }
          stream << std::endl;
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
            stream << this->astCtxt->assert_(*it) << std::endl;
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
