/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef   EFLAGSEXPRESSIONS_H
#define   EFLAGSEXPRESSIONS_H

#include "AnalysisProcessor.h"
#include "SMT2Lib.h"
#include "SymbolicExpression.h"


/* Retunrs the flag expression */
namespace EflagsExpressions {

  smt2lib::smtAstAbstractNode *af(SymbolicExpression *parent, uint32 bvSize, smt2lib::smtAstAbstractNode *op1, smt2lib::smtAstAbstractNode *op2);
  smt2lib::smtAstAbstractNode *afNeg(SymbolicExpression *parent, uint32 bvSize, smt2lib::smtAstAbstractNode *op1);

  smt2lib::smtAstAbstractNode *cfAdd(SymbolicExpression *parent, uint32 bvSize, smt2lib::smtAstAbstractNode *op1);
  smt2lib::smtAstAbstractNode *cfImul(SymbolicExpression *parent, uint32 bvSize, smt2lib::smtAstAbstractNode *mulRes);
  smt2lib::smtAstAbstractNode *cfMul(uint32 bvSize, smt2lib::smtAstAbstractNode *up);
  smt2lib::smtAstAbstractNode *cfNeg(uint32 bvSize, smt2lib::smtAstAbstractNode *op1);
  smt2lib::smtAstAbstractNode *cfRcl(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, smt2lib::smtAstAbstractNode *op2);
  smt2lib::smtAstAbstractNode *cfRol(SymbolicExpression *parent, AnalysisProcessor &ap, smt2lib::smtAstAbstractNode *op2);
  smt2lib::smtAstAbstractNode *cfRor(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, smt2lib::smtAstAbstractNode *op2);
  smt2lib::smtAstAbstractNode *cfSar(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, smt2lib::smtAstAbstractNode *op1, smt2lib::smtAstAbstractNode *op2);
  smt2lib::smtAstAbstractNode *cfShl(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, smt2lib::smtAstAbstractNode *op1, smt2lib::smtAstAbstractNode *op2);
  smt2lib::smtAstAbstractNode *cfShr(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, smt2lib::smtAstAbstractNode *op1, smt2lib::smtAstAbstractNode *op2);
  smt2lib::smtAstAbstractNode *cfSub(SymbolicExpression *parent, uint32 bvSize, smt2lib::smtAstAbstractNode *op1, smt2lib::smtAstAbstractNode *op2);

  smt2lib::smtAstAbstractNode *clearFlag(void);

  smt2lib::smtAstAbstractNode *ofAdd(SymbolicExpression *parent, uint32 extractSize, smt2lib::smtAstAbstractNode *op1, smt2lib::smtAstAbstractNode *op2);
  smt2lib::smtAstAbstractNode *ofImul(SymbolicExpression *parent, uint32 bvSize, smt2lib::smtAstAbstractNode *mulRes);
  smt2lib::smtAstAbstractNode *ofMul(uint32 bvSize, smt2lib::smtAstAbstractNode *up);
  smt2lib::smtAstAbstractNode *ofNeg(SymbolicExpression *parent, uint32 bvSize, smt2lib::smtAstAbstractNode *op1);
  smt2lib::smtAstAbstractNode *ofRol(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, smt2lib::smtAstAbstractNode *op2);
  smt2lib::smtAstAbstractNode *ofRor(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, smt2lib::smtAstAbstractNode *op2);
  smt2lib::smtAstAbstractNode *ofSar(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, smt2lib::smtAstAbstractNode *op2);
  smt2lib::smtAstAbstractNode *ofShl(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, smt2lib::smtAstAbstractNode *op1, smt2lib::smtAstAbstractNode *op2);
  smt2lib::smtAstAbstractNode *ofShr(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, smt2lib::smtAstAbstractNode *op1, smt2lib::smtAstAbstractNode *op2);
  smt2lib::smtAstAbstractNode *ofSub(SymbolicExpression *parent, uint32 extractSize, smt2lib::smtAstAbstractNode *op1, smt2lib::smtAstAbstractNode *op2);

  smt2lib::smtAstAbstractNode *pf(SymbolicExpression *parent, uint32 bvSizes);
  smt2lib::smtAstAbstractNode *pfShl(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, smt2lib::smtAstAbstractNode *op2);

  smt2lib::smtAstAbstractNode *setFlag(void);

  smt2lib::smtAstAbstractNode *sf(SymbolicExpression *parent, uint32 extractSize);
  smt2lib::smtAstAbstractNode *sfShl(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, uint32 extractSize, smt2lib::smtAstAbstractNode *op2);

  smt2lib::smtAstAbstractNode *zf(SymbolicExpression *parent, uint32 bvSize);
  smt2lib::smtAstAbstractNode *zfShl(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, smt2lib::smtAstAbstractNode *op2);
}


#endif     /* !__EFLAGSEXPRESSIONS_H__ */
