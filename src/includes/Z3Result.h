/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef Z3RESULT_H
#define Z3RESULT_H

#include <z3++.h>

#include "TritonTypes.h"

class Z3Result {
  public:
    Z3Result();
    ~Z3Result();
    Z3Result(const Z3Result& copy);

    void printExpr(void) const;
    void setExpr(z3::expr& expr);

    z3::context&  getContext(void);
    z3::expr&     getExpr(void);
    std::string   getStringValue(void) const;
    uint64        getUint64Value(void) const;

  private:
    z3::context context;
    z3::expr expr;
};

#endif /* Z3RESULT_H */
