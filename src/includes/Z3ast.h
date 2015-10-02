/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef Z3AST_H
#define Z3AST_H

#include <z3++.h>

#include "Visitor.h"
#include "SMT2Lib.h"
#include "TritonTypes.h"
#include "Z3Result.h"
#include "AnalysisProcessor.h"

class AnalysisProcessor;
extern AnalysisProcessor ap;


class Z3ast : public Visitor {
  public:
    Z3ast();
    ~Z3ast();

    virtual Z3Result& eval(smt2lib::smtAstAbstractNode& e);

    virtual void operator()(smt2lib::smtAstAbstractNode& e);

    virtual void operator()(smt2lib::smtAstAssertNode& e);
    virtual void operator()(smt2lib::smtAstBvaddNode& e);
    virtual void operator()(smt2lib::smtAstBvandNode& e);
    virtual void operator()(smt2lib::smtAstBvashrNode& e);
    virtual void operator()(smt2lib::smtAstBvlshrNode& e);
    virtual void operator()(smt2lib::smtAstBvmulNode& e);
    virtual void operator()(smt2lib::smtAstBvsmodNode& e);
    virtual void operator()(smt2lib::smtAstBvnandNode& e);
    virtual void operator()(smt2lib::smtAstBvnegNode& e);
    virtual void operator()(smt2lib::smtAstBvnorNode& e);
    virtual void operator()(smt2lib::smtAstBvnotNode& e);
    virtual void operator()(smt2lib::smtAstBvorNode& e);
    virtual void operator()(smt2lib::smtAstBvrolNode& e);
    virtual void operator()(smt2lib::smtAstBvrorNode& e);
    virtual void operator()(smt2lib::smtAstBvsdivNode& e);
    virtual void operator()(smt2lib::smtAstBvsgeNode& e);
    virtual void operator()(smt2lib::smtAstBvsgtNode& e);
    virtual void operator()(smt2lib::smtAstBvshlNode& e);
    virtual void operator()(smt2lib::smtAstBvsleNode& e);
    virtual void operator()(smt2lib::smtAstBvsltNode& e);
    virtual void operator()(smt2lib::smtAstBvsremNode& e);
    virtual void operator()(smt2lib::smtAstBvsubNode& e);
    virtual void operator()(smt2lib::smtAstBvudivNode& e);
    virtual void operator()(smt2lib::smtAstBvugeNode& e);
    virtual void operator()(smt2lib::smtAstBvugtNode& e);
    virtual void operator()(smt2lib::smtAstBvuleNode& e);
    virtual void operator()(smt2lib::smtAstBvultNode& e);
    virtual void operator()(smt2lib::smtAstBvuremNode& e);
    virtual void operator()(smt2lib::smtAstBvxnorNode& e);
    virtual void operator()(smt2lib::smtAstBvxorNode& e);
    virtual void operator()(smt2lib::smtAstBvNode& e);
    virtual void operator()(smt2lib::smtAstCompoundNode& e);
    virtual void operator()(smt2lib::smtAstConcatNode& e);
    virtual void operator()(smt2lib::smtAstDecimalNode& e);
    virtual void operator()(smt2lib::smtAstDeclareNode& e);
    virtual void operator()(smt2lib::smtAstDistinctNode& e);
    virtual void operator()(smt2lib::smtAstEqualNode& e);
    virtual void operator()(smt2lib::smtAstExtractNode& e);
    virtual void operator()(smt2lib::smtAstIteNode& e);
    virtual void operator()(smt2lib::smtAstReferenceNode& e);
    virtual void operator()(smt2lib::smtAstStringNode& e);
    virtual void operator()(smt2lib::smtAstSxNode& e);
    virtual void operator()(smt2lib::smtAstVariableNode& e);
    virtual void operator()(smt2lib::smtAstZxNode& e);

  private:
    Z3Result result;
};

#endif /* EVALUATORSMT_H */
#endif /* LIGHT_VERSION */

