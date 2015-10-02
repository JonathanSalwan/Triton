/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <Z3Result.h>


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


std::string Z3Result::getStringValue() const {
  z3::expr sExpr = this->expr.simplify();
  return Z3_get_numeral_string(this->context, sExpr);
}


uint64 Z3Result::getUint64Value(void) const {
  uint64 result = 0;

  if (!this->expr.is_int())
    throw std::runtime_error("getUint64Value: The ast is not a numerical value");

  Z3_get_numeral_uint64(this->context, this->expr, &result);

  return result;
}


z3::context& Z3Result::getContext(void) {
  return this->context;
}


void Z3Result::printExpr(void) const {
  std::cout << this->expr << std::endl;
}

#endif /* LIGHT_VERSION */

