//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/z3Result.hpp>



namespace triton {
  namespace ast {

    Z3Result::Z3Result()
      : context(), expr(this->context) {
    }


    Z3Result::~Z3Result() {
    }


    Z3Result::Z3Result(const Z3Result& copy)
      : expr(copy.expr) {
    }


    void Z3Result::setExpr(z3::expr& expr) {
      this->expr = expr;
    }


    z3::expr& Z3Result::getExpr(void) {
      return this->expr;
    }


    triton::uint32 Z3Result::getBitvectorSize(void) {
      return this->expr.get_sort().bv_size();
    }


    std::string Z3Result::getStringValue() const {
      z3::expr sExpr = this->expr.simplify();
      return Z3_get_numeral_string(this->context, sExpr);
    }


    triton::__uint Z3Result::getUintValue(void) const {
      triton::__uint result = 0;

      if (!this->expr.is_int())
        throw triton::exceptions::Exception("Z3Result::getUintValue(): The ast is not a numerical value.");

      #if defined(__x86_64__) || defined(_M_X64)
      Z3_get_numeral_uint64(this->context, this->expr, &result);
      #endif
      #if defined(__i386) || defined(_M_IX86)
      Z3_get_numeral_uint(this->context, this->expr, &result);
      #endif

      return result;
    }


    z3::context& Z3Result::getContext(void) {
      return this->context;
    }


    void Z3Result::printExpr(void) const {
      std::cout << this->expr << std::endl;
    }

  }; /* ast namespace */
}; /* triton namespace */
