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


namespace SymExpr
{
  /* Defines the kind of the symbolic expression */
  enum kind {
    UNDEF = 0,
    REG,
    MEM
  };
};


/* Symbolic expression */
class SymbolicExpression {

  private:
    enum SymExpr::kind          kind;
    smt2lib::smtAstAbstractNode *expression;
    std::string                 comment;
    __uint                      id;

  public:
    bool                        isTainted;

    __uint                      getID(void);
    bool                        isMem(void);
    bool                        isReg(void);
    enum SymExpr::kind          getKind(void);
    smt2lib::smtAstAbstractNode *getExpression(void);
    std::string                 getComment(void);
    std::string                 getID2Str(void);
    void                        setExpression(smt2lib::smtAstAbstractNode *expr);
    void                        setKind(enum SymExpr::kind k);

    SymbolicExpression(smt2lib::smtAstAbstractNode *expr, __uint id, enum SymExpr::kind);
    SymbolicExpression(smt2lib::smtAstAbstractNode *expr, __uint id, enum SymExpr::kind, std::string comment);
    ~SymbolicExpression();
};

#endif /* !_SYMBOLICEXPRESSION_H_ */
#endif /* LIGHT_VERSION */

