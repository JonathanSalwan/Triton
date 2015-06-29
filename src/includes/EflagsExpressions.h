#ifndef   EFLAGSEXPRESSIONS_H
#define   EFLAGSEXPRESSIONS_H

#include "AnalysisProcessor.h"
#include "SMT2Lib.h"
#include "SymbolicExpression.h"


/* Retunrs the flag expression */
namespace EflagsExpressions {

  std::string af(SymbolicExpression *parent, uint32 bvSize, std::stringstream &op1, std::stringstream &op2);
  std::string afNeg(SymbolicExpression *parent, uint32 bvSize, std::stringstream &op1);

  std::string cfAdd(SymbolicExpression *parent, std::stringstream &op1);
  std::string cfImul(SymbolicExpression *parent, std::stringstream &op1);
  std::string cfMul(uint32 bvSize, std::stringstream &up);
  std::string cfNeg(uint32 bvSize, std::stringstream &op1);
  std::string cfRcl(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op2);
  std::string cfRol(SymbolicExpression *parent, AnalysisProcessor &ap, std::stringstream &op2);
  std::string cfRor(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op2);
  std::string cfSar(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op1, std::stringstream &op2);
  std::string cfShl(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op1, std::stringstream &op2);
  std::string cfShr(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op1, std::stringstream &op2);
  std::string cfSub(std::stringstream &op1, std::stringstream &op2);

  std::string clearFlag(void);

  std::string ofAdd(SymbolicExpression *parent, uint32 extractSize, std::stringstream &op1, std::stringstream &op2);
  std::string ofImul(SymbolicExpression *parent, std::stringstream &op1);
  std::string ofMul(uint32 bvSize, std::stringstream &up);
  std::string ofNeg(SymbolicExpression *parent, uint32 bvSize, std::stringstream &op1);
  std::string ofRol(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op2);
  std::string ofRor(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op2);
  std::string ofSar(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op2);
  std::string ofShl(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op1, std::stringstream &op2);
  std::string ofShr(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op1, std::stringstream &op2);
  std::string ofSub(SymbolicExpression *parent, uint32 extractSize, std::stringstream &op1, std::stringstream &op2);

  std::string pf(SymbolicExpression *parent);
  std::string pfShl(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op2);

  std::string setFlag(void);

  std::string sf(SymbolicExpression *parent, uint32 extractSize);
  std::string sfShl(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, uint32 extractSize, std::stringstream &op2);

  std::string zf(SymbolicExpression *parent, uint32 bvSize);
  std::string zfShl(SymbolicExpression *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op2);
}


#endif     /* !__EFLAGSEXPRESSIONS_H__ */
