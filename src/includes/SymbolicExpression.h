/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef SYMBOLICEXPRESSION_H
#define SYMBOLICEXPRESSION_H

#include <stdint.h>

#include <sstream>
#include <string>

#include "SMT2Lib.h"
#include "TritonTypes.h"


/* Symbolic expression */
class SymbolicExpression {

  private:
    smt2lib::smtAstAbstractNode *expression;
    std::string                 comment;
    uint64                      id;

  public:
    bool                        isTainted;
    smt2lib::smtAstAbstractNode *getExpression(void);
    std::string                 getComment(void);
    std::string                 getID2Str(void);
    uint64                      getID(void);
    void                        setExpression(smt2lib::smtAstAbstractNode *expr);

    SymbolicExpression(smt2lib::smtAstAbstractNode *expr, uint64 id);
    SymbolicExpression(smt2lib::smtAstAbstractNode *expr, uint64 id, std::string comment);
    ~SymbolicExpression();
};

#endif /* !_SYMBOLICEXPRESSION_H_ */
#endif /* LIGHT_VERSION */

