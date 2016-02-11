//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <list>

#include <smt2libZ3ToTritonAst.hpp>



namespace triton {
  namespace smt2lib {

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


    smtAstAbstractNode* Z3ToTritonAst::convert(void) {
      return this->visit(this->expr);
    }


    smtAstAbstractNode* Z3ToTritonAst::visit(z3::expr const& expr) {
      smtAstAbstractNode* node = nullptr;

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
          node = triton::smt2lib::equal(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_DISTINCT: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_DISTINCT must conatin two arguments.");
          node = triton::smt2lib::distinct(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_ITE: {
          if (expr.num_args() != 3)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_ITE must conatin three arguments.");
          node = triton::smt2lib::ite(this->visit(expr.arg(0)), this->visit(expr.arg(1)), this->visit(expr.arg(2)));
          break;
        }

        case Z3_OP_AND: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_AND must conatin two arguments.");
          node = triton::smt2lib::land(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_OR: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_OR must conatin two arguments.");
          node = triton::smt2lib::lor(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_BNUM: {
          std::string stringValue = Z3_get_numeral_string(this->context, expr);
          triton::uint128 intValue{stringValue};
          node = triton::smt2lib::bv(intValue, expr.get_sort().bv_size());
          break;
        }

        case Z3_OP_BNEG: {
          if (expr.num_args() != 1)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BNEG must conatin one argument.");
          node = triton::smt2lib::bvneg(this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_BADD: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BADD must conatin two arguments.");
          node = triton::smt2lib::bvadd(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_BSUB: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BSUB must conatin two arguments.");
          node = triton::smt2lib::bvsub(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_BMUL: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BMUL must conatin two arguments.");
          node = triton::smt2lib::bvmul(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_BSDIV: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BSDIV must conatin two arguments.");
          node = triton::smt2lib::bvsdiv(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_BUDIV: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BUDIV must conatin two arguments.");
          node = triton::smt2lib::bvudiv(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_BSREM: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BSREM must conatin two arguments.");
          node = triton::smt2lib::bvsrem(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_BUREM: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BUREM must conatin two arguments.");
          node = triton::smt2lib::bvurem(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_BSMOD: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BSMOD must conatin two arguments.");
          node = triton::smt2lib::bvsmod(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_ULEQ: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_ULEQ must conatin two arguments.");
          node = triton::smt2lib::bvule(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_SLEQ: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_SLEQ must conatin two arguments.");
          node = triton::smt2lib::bvsle(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_UGEQ: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_UGEQ must conatin two arguments.");
          node = triton::smt2lib::bvuge(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_SGEQ: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_SGEQ must conatin two arguments.");
          node = triton::smt2lib::bvsge(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_ULT: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_ULT must conatin two arguments.");
          node = triton::smt2lib::bvult(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_SLT: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_SLT must conatin two arguments.");
          node = triton::smt2lib::bvslt(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_UGT: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_UGT must conatin two arguments.");
          node = triton::smt2lib::bvugt(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_SGT: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_SGT must conatin two arguments.");
          node = triton::smt2lib::bvsgt(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_BAND: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BAND must conatin two arguments.");
          node = triton::smt2lib::bvand(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_BOR: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BOR must conatin two arguments.");
          node = triton::smt2lib::bvor(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_BNOT: {
          if (expr.num_args() != 1)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BNOT must conatin one argument.");
          node = triton::smt2lib::bvnot(this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_BXOR: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BXOR must conatin two arguments.");
          node = triton::smt2lib::bvxor(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_BNAND: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BNAND must conatin two arguments.");
          node = triton::smt2lib::bvnand(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_BNOR: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BNOR must conatin two arguments.");
          node = triton::smt2lib::bvnor(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_BXNOR: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BXNOR must conatin two arguments.");
          node = triton::smt2lib::bvxnor(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_CONCAT: {
          if (expr.num_args() < 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_CONCAT must conatin at leat two arguments.");

          std::list<smtAstAbstractNode*> args;
          for (triton::uint32 i = 0; i < expr.num_args(); i++) {
            args.push_back(this->visit(expr.arg(i)));
          }

          node = triton::smt2lib::concat(args);
          break;
        }

        case Z3_OP_SIGN_EXT: {
          if (expr.num_args() != 1)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_SIGN_EXT must conatin one argument.");
          node = triton::smt2lib::sx(expr.hi(), this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_ZERO_EXT: {
          if (expr.num_args() != 1)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_ZERO_EXT must conatin one argument.");
          node = triton::smt2lib::zx(expr.hi(), this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_EXTRACT: {
          if (expr.num_args() != 1)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_EXTRACT must conatin one argument.");
          node = triton::smt2lib::extract(expr.hi(), expr.lo(), this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_BSHL: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BSHL must conatin two arguments.");
          node = triton::smt2lib::bvshl(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_BLSHR: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BLSHR must conatin two arguments.");
          node = triton::smt2lib::bvlshr(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_BASHR: {
          if (expr.num_args() != 2)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_BASHR must conatin two arguments.");
          node = triton::smt2lib::bvashr(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_ROTATE_LEFT: {
          if (expr.num_args() != 1)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_ROTATE_LEFT must conatin one argument.");
          node = triton::smt2lib::bvrol(expr.hi(), this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_ROTATE_RIGHT: {
          if (expr.num_args() != 1)
            throw std::runtime_error("Z3ToTritonAst::visit(): Z3_OP_ROTATE_RIGHT must conatin one argument.");
          node = triton::smt2lib::bvror(expr.hi(), this->visit(expr.arg(0)));
          break;
        }

        /* Variable? */
        case 0x82d: {
          node = triton::smt2lib::variable(function.name().str());
          break;
        }

        default:
          throw std::runtime_error("Z3ToTritonAst::visit(): '" + function.name().str() + "' AST node not supported yet");
      }

      return node;
    }


  }; /* smt2lib namespace */
}; /* triton namespace */

