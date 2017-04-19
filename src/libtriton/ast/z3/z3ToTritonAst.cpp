//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <list>

#include <triton/exceptions.hpp>
#include <triton/z3ToTritonAst.hpp>
#include <triton/astContext.hpp>



namespace triton {
  namespace ast {

    Z3ToTritonAst::Z3ToTritonAst(triton::engines::symbolic::SymbolicEngine* symbolicEngine, AstContext& astCtxt)
      : symbolicEngine(symbolicEngine), astCtxt(astCtxt), context(), expr(this->context) {
      if (symbolicEngine == nullptr)
        throw triton::exceptions::AstTranslations("Z3ToTritonAst::Z3ToTritonAst(): The symbolicEngine API cannot be null.");
    }


    Z3ToTritonAst::Z3ToTritonAst(triton::engines::symbolic::SymbolicEngine* symbolicEngine, const z3::expr& expr, AstContext& astCtxt)
      : symbolicEngine(symbolicEngine)
        , astCtxt(astCtxt)
        , context()
        , expr(expr)
    {
      if (symbolicEngine == nullptr)
        throw triton::exceptions::AstTranslations("Z3ToTritonAst::Z3ToTritonAst(): The symbolicEngine API cannot be null.");
    }

    void Z3ToTritonAst::setExpr(z3::expr& expr) {
      this->expr = expr;
    }


    AbstractNode* Z3ToTritonAst::convert(void) {
      return this->visit(this->expr);
    }


    AbstractNode* Z3ToTritonAst::visit(const z3::expr& expr) {
      AbstractNode* node = nullptr;

      /* Currently, only support application node */
      if (expr.is_quantifier())
        throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Quantifier not supported yet.");

      if (!expr.is_app())
        throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): At this moment only application are supported.");

      /* Get the function declaration */
      z3::func_decl function = expr.decl();

      /* All z3's AST nodes supported */
      switch (function.decl_kind()) {

        case Z3_OP_EQ: {
          if (expr.num_args() != 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_EQ must contain two arguments.");
          node = astCtxt.equal(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          break;
        }

        case Z3_OP_DISTINCT: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_DISTINCT must contain at least two arguments.");
          node = astCtxt.distinct(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.distinct(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_ITE: {
          if (expr.num_args() != 3)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_ITE must contain three arguments.");
          node = astCtxt.ite(this->visit(expr.arg(0)), this->visit(expr.arg(1)), this->visit(expr.arg(2)));
          break;
        }

        case Z3_OP_AND: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_AND must contain at least two arguments.");
          node = astCtxt.land(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.land(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_OR: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_OR must contain at least two arguments.");
          node = astCtxt.lor(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.lor(node, this->visit(expr.arg(i)));
          break;
        }


        case Z3_OP_NOT: {
          if (expr.num_args() != 1)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_NOT must contain one argument.");
          node = astCtxt.lnot(this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_BNUM: {
          std::string stringValue = Z3_get_numeral_string(this->context, expr);
          triton::uint512 intValue{stringValue};
          node = astCtxt.bv(intValue, expr.get_sort().bv_size());
          break;
        }

        case Z3_OP_BNEG: {
          if (expr.num_args() != 1)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BNEG must contain one argument.");
          node = astCtxt.bvneg(this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_BADD: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BADD must contain at least two arguments.");
          node = astCtxt.bvadd(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvadd(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BSUB: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BSUB must contain at least two arguments.");
          node = astCtxt.bvsub(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvsub(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BMUL: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BMUL must contain at least two arguments.");
          node = astCtxt.bvmul(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvmul(node, this->visit(expr.arg(i)));
          break;
        }

        //case Z3_OP_BSDIV_I:
        case Z3_OP_BSDIV: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BSDIV must contain at least two arguments.");
          node = astCtxt.bvsdiv(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvsdiv(node, this->visit(expr.arg(i)));
          break;
        }

        //case Z3_OP_BUDIV_I:
        case Z3_OP_BUDIV: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BUDIV must contain at least two arguments.");
          node = astCtxt.bvudiv(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvudiv(node, this->visit(expr.arg(i)));
          break;
        }

        //case Z3_OP_BSREM_I:
        case Z3_OP_BSREM: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BSREM must contain at least two arguments.");
          node = astCtxt.bvsrem(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvsrem(node, this->visit(expr.arg(i)));
          break;
        }

        //case Z3_OP_BUREM_I:
        case Z3_OP_BUREM: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BUREM must contain at least two arguments.");
          node = astCtxt.bvurem(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvurem(node, this->visit(expr.arg(i)));
          break;
        }

        //case Z3_OP_BSMOD_I:
        case Z3_OP_BSMOD: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BSMOD must contain at least two arguments.");
          node = astCtxt.bvsmod(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvsmod(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_ULEQ: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_ULEQ must contain at least two arguments.");
          node = astCtxt.bvule(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvule(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_SLEQ: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_SLEQ must contain at least two arguments.");
          node = astCtxt.bvsle(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvsle(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_UGEQ: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_UGEQ must contain at least two arguments.");
          node = astCtxt.bvuge(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvuge(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_SGEQ: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_SGEQ must contain at least two arguments.");
          node = astCtxt.bvsge(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvsge(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_ULT: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_ULT must contain at least two arguments.");
          node = astCtxt.bvult(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvult(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_SLT: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_SLT must contain at least two arguments.");
          node = astCtxt.bvslt(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvslt(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_UGT: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_UGT must contain at least two arguments.");
          node = astCtxt.bvugt(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvugt(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_SGT: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_SGT must contain at least two arguments.");
          node = astCtxt.bvsgt(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvsgt(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BAND: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BAND must contain at least two arguments.");
          node = astCtxt.bvand(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvand(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BOR: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BOR must contain at least two arguments.");
          node = astCtxt.bvor(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvor(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BNOT: {
          if (expr.num_args() != 1)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BNOT must contain one argument.");
          node = astCtxt.bvnot(this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_BXOR: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BXOR must contain at least two arguments.");
          node = astCtxt.bvxor(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvxor(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BNAND: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BNAND must contain at least two arguments.");
          node = astCtxt.bvnand(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvnand(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BNOR: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BNOR must contain at least two arguments.");
          node = astCtxt.bvnor(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvnor(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BXNOR: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BXNOR must contain at least two arguments.");
          node = astCtxt.bvxnor(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvxnor(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_CONCAT: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_CONCAT must contain at least two arguments.");

          std::list<AbstractNode*> args;
          for (triton::uint32 i = 0; i < expr.num_args(); i++) {
            args.push_back(this->visit(expr.arg(i)));
          }

          node = astCtxt.concat(args);
          break;
        }

        case Z3_OP_SIGN_EXT: {
          if (expr.num_args() != 1)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_SIGN_EXT must contain one argument.");
          node = astCtxt.sx(expr.hi(), this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_ZERO_EXT: {
          if (expr.num_args() != 1)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_ZERO_EXT must contain one argument.");
          node = astCtxt.zx(expr.hi(), this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_EXTRACT: {
          if (expr.num_args() != 1)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_EXTRACT must contain one argument.");
          node = astCtxt.extract(expr.hi(), expr.lo(), this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_BSHL: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BSHL must contain at least two arguments.");
          node = astCtxt.bvshl(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvshl(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BLSHR: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BLSHR must contain at least two arguments.");
          node = astCtxt.bvlshr(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvlshr(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_BASHR: {
          if (expr.num_args() < 2)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_BASHR must contain at least two arguments.");
          node = astCtxt.bvashr(this->visit(expr.arg(0)), this->visit(expr.arg(1)));
          for (triton::uint32 i = 2; i < expr.num_args(); i++)
            node = astCtxt.bvashr(node, this->visit(expr.arg(i)));
          break;
        }

        case Z3_OP_ROTATE_LEFT: {
          if (expr.num_args() != 1)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_ROTATE_LEFT must contain one argument.");
          node = astCtxt.bvrol(expr.hi(), this->visit(expr.arg(0)));
          break;
        }

        case Z3_OP_ROTATE_RIGHT: {
          if (expr.num_args() != 1)
            throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): Z3_OP_ROTATE_RIGHT must contain one argument.");
          node = astCtxt.bvror(expr.hi(), this->visit(expr.arg(0)));
          break;
        }

        /* Variable or string */
        case Z3_OP_UNINTERPRETED: {
          std::string name = function.name().str();
          triton::engines::symbolic::SymbolicVariable* symVar = this->symbolicEngine->getSymbolicVariableFromName(name);

          if (symVar)
            node = astCtxt.variable(*symVar);
          else
            node = astCtxt.string(name);

          break;
        }

        default:
          throw triton::exceptions::AstTranslations("Z3ToTritonAst::visit(): '" + function.name().str() + "' AST node not supported yet");
      }

      return node;
    }


  }; /* ast namespace */
}; /* triton namespace */
