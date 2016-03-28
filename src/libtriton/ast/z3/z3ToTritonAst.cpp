//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <list>

#include <api.hpp>
#include <symbolicVariable.hpp>
#include <z3ToTritonAst.hpp>



namespace triton {
  namespace ast {

    Z3ToTritonAst::Z3ToTritonAst()
      : context(), expr(this->context) {
    }


    Z3ToTritonAst::Z3ToTritonAst(z3::expr& expr)
      : context(), expr(this->context) {
      this->expr = expr;
    }


    Z3ToTritonAst::Z3ToTritonAst(const Z3ToTritonAst& copy)
      : expr(copy.expr) {
    }


    Z3ToTritonAst::~Z3ToTritonAst() {
    }


    void Z3ToTritonAst::setExpr(z3::expr& expr) {
      this->expr = expr;
    }


    AbstractNode* Z3ToTritonAst::convert(void) {
      return this->visit(this->expr);
    }


    AbstractNode* Z3ToTritonAst::visit(z3::expr const& expr) {
      AbstractNode* node = nullptr;

      /* Currently, only support application node */
      if (expr.is_quantifier())
        throw std::runtime_error("Z3ToTritonAst::visit(): Quantifier not supported yet.");

      if (!expr.is_app())
        throw std::runtime_error("Z3ToTritonAst::visit(): At this moment only application are supported.");

      /* Get the function declaration */
      z3::func_decl function = expr.decl();

      /* All z3's AST nodes supported */
      switch (function.decl_kind()) {

        case Z3_OP_EQ: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_EQ must conatin two arguments.");
          node = triton::ast::equal(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_DISTINCT: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_DISTINCT must conatin at least two arguments.");
          node = triton::ast::distinct(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::distinct(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_ITE: {
          if (expr.num_args() != 3)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_ITE must conatin three arguments.");
          node = triton::ast::ite(this->visit(expr.arg(0)), this->visit(expr.arg(1)), this->visit(expr.arg(2)));
          break;
        }

        case Z3_OP_AND: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_AND must conatin at least two arguments.");
          node = triton::ast::land(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::land(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_OR: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_OR must conatin at least two arguments.");
          node = triton::ast::lor(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::lor(node, this->visit(expr.arg(i)));
          break;
        }


        case Z3_OP_NOT: {
          if (expr.num_args() != 1)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_NOT must conatin at one argument.");
          node = triton::ast::lnot(this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_BNUM: {
          std::string stringValue = Z3_get_numeral_string(this->context, expr);
          triton::uint512 intValue{stringValue};
          node = triton::ast::bv(intValue, expr.get_sort().bv_size());
          break;
        }

        case Z3_OP_BNEG: {
          if (expr.num_args() != 1)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BNEG must conatin one argument.");
          node = triton::ast::bvneg(this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_BADD: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BADD must conatin at least two arguments.");
          node = triton::ast::bvadd(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvadd(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BSUB: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BSUB must conatin at least two arguments.");
          node = triton::ast::bvsub(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvsub(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BMUL: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BMUL must conatin at least two arguments.");
          node = triton::ast::bvmul(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvmul(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BSDIV: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BSDIV must conatin at least two arguments.");
          node = triton::ast::bvsdiv(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvsdiv(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BUDIV: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BUDIV must conatin at least two arguments.");
          node = triton::ast::bvudiv(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvudiv(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BSREM: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BSREM must conatin at least two arguments.");
          node = triton::ast::bvsrem(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvsrem(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BUREM: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BUREM must conatin at least two arguments.");
          node = triton::ast::bvurem(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvurem(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BSMOD: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BSMOD must conatin at least two arguments.");
          node = triton::ast::bvsmod(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvsmod(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_ULEQ: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_ULEQ must conatin at least two arguments.");
          node = triton::ast::bvule(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvule(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_SLEQ: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_SLEQ must conatin at least two arguments.");
          node = triton::ast::bvsle(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvsle(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_UGEQ: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_UGEQ must conatin at least two arguments.");
          node = triton::ast::bvuge(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvuge(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_SGEQ: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_SGEQ must conatin at least two arguments.");
          node = triton::ast::bvsge(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvsge(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_ULT: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_ULT must conatin at least two arguments.");
          node = triton::ast::bvult(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvult(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_SLT: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_SLT must conatin at least two arguments.");
          node = triton::ast::bvslt(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvslt(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_UGT: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_UGT must conatin at least two arguments.");
          node = triton::ast::bvugt(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvugt(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_SGT: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_SGT must conatin at least two arguments.");
          node = triton::ast::bvsgt(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvsgt(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BAND: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BAND must conatin at least two arguments.");
          node = triton::ast::bvand(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvand(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BOR: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BOR must conatin at least two arguments.");
          node = triton::ast::bvor(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvor(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BNOT: {
          if (expr.num_args() != 1)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BNOT must conatin one argument.");
          node = triton::ast::bvnot(this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_BXOR: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BXOR must conatin at least two arguments.");
          node = triton::ast::bvxor(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvxor(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BNAND: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BNAND must conatin at least two arguments.");
          node = triton::ast::bvnand(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvnand(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BNOR: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BNOR must conatin at least two arguments.");
          node = triton::ast::bvnor(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvnor(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BXNOR: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BXNOR must conatin at least two arguments.");
          node = triton::ast::bvxnor(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvxnor(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_CONCAT: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_CONCAT must conatin at leat two arguments.");

          std::list<AbstractNode*> args;
          for (triton::uint32 i = 0; i < expr.num_args(); i++) {
            args.push_back(this->visit(expr.arg(i)));
          }

          node = triton::ast::concat(args);
          break;
        }

        case Z3_OP_SIGN_EXT: {
          if (expr.num_args() != 1)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_SIGN_EXT must conatin one argument.");
          node = triton::ast::sx(expr.hi(), this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_ZERO_EXT: {
          if (expr.num_args() != 1)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_ZERO_EXT must conatin one argument.");
          node = triton::ast::zx(expr.hi(), this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_EXTRACT: {
          if (expr.num_args() != 1)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_EXTRACT must conatin one argument.");
          node = triton::ast::extract(expr.hi(), expr.lo(), this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_BSHL: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BSHL must conatin at least two arguments.");
          node = triton::ast::bvshl(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvshl(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BLSHR: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BLSHR must conatin at least two arguments.");
          node = triton::ast::bvlshr(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvlshr(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BASHR: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BASHR must conatin at least two arguments.");
          node = triton::ast::bvashr(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = triton::ast::bvashr(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_ROTATE_LEFT: {
          if (expr.num_args() != 1)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_ROTATE_LEFT must conatin one argument.");
          node = triton::ast::bvrol(expr.hi(), this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_ROTATE_RIGHT: {
          if (expr.num_args() != 1)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_ROTATE_RIGHT must conatin one argument.");
          node = triton::ast::bvror(expr.hi(), this->visit(expr.arg(0)));
          break;
        }

        /* Variable or string */
        case Z3_OP_UNINTERPRETED: {
          std::string name = function.name().str();
          triton::engines::symbolic::SymbolicVariable* symVar = triton::api.getSymbolicVariableFromName(name);

          if (symVar)
            node = triton::ast::variable(*symVar);
          else
            node = triton::ast::string(name);

          break;
        }

        default:
          throw std::runtime_error("Z3ToTritonAst::visit(): '" + function.name().str() + "' AST node not supported yet");
      }

      return node;
    }


  }; /* ast namespace */
}; /* triton namespace */

