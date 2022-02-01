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
#include <triton/liftingToPython.hpp>
#include <triton/tritonTypes.hpp>



namespace triton {
  namespace engines {
    namespace lifters {

      LiftingToPython::LiftingToPython(const triton::ast::SharedAstContext& astCtxt, triton::engines::symbolic::SymbolicEngine* symbolic)
        : astCtxt(astCtxt), symbolic(symbolic) {
      }


      void LiftingToPython::requiredFunctions(std::ostream& stream) {
        stream << "def sx(bits, value):" << std::endl;
        stream << "    sign_bit = 1 << (bits - 1)" << std::endl;
        stream << "    return (value & (sign_bit - 1)) - (value & sign_bit)" << std::endl;

        stream << std::endl;
        stream << "def rol(value, rot, bits):" << std::endl;
        stream << "    return ((value << rot) | (value >> (bits - rot))) & ((0b1 << bits) - 1)" << std::endl;

        stream << std::endl;
        stream << "def ror(value, rot, bits):" << std::endl;
        stream << "    return ((value >> rot) | (value << (bits - rot))) & ((0b1 << bits) - 1)" << std::endl;

        stream << std::endl;
        stream << "def forall(variables, expr):" << std::endl;
        stream << "    return True" << std::endl;

        stream << std::endl;
      }


      std::ostream& LiftingToPython::liftToPython(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr) {
        /* Save the AST representation mode */
        triton::ast::representations::mode_e mode = this->astCtxt->getRepresentationMode();
        this->astCtxt->setRepresentationMode(triton::ast::representations::PYTHON_REPRESENTATION);

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

        /* Print symbolic variables */
        for (const auto& var : symVars) {
          auto n = this->astCtxt->declare(this->astCtxt->variable(var.second));
          this->astCtxt->print(stream, n.get());
          stream << std::endl;
        }

        /* Sort SSA */
        std::sort(symExprs.begin(), symExprs.end());

        /* Print symbolic expressions */
        for (const auto& id : symExprs) {
          stream << ssa[id]->getFormattedExpression() << std::endl;
        }

        /* Restore the AST representation mode */
        this->astCtxt->setRepresentationMode(mode);

        return stream;
      }

    }; /* lifters namespace */
  }; /* engines namespace */
}; /* triton namespace */
