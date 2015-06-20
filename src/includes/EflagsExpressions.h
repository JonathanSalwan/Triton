#ifndef   EFLAGSEXPRESSIONS_H
#define   EFLAGSEXPRESSIONS_H

#include "AnalysisProcessor.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


/* Retunrs the flag expression */
namespace EflagsExpressions {

  std::string af(SymbolicElement *parent, uint32 bvSize, std::stringstream &op1, std::stringstream &op2);
  std::string afNeg(SymbolicElement *parent, uint32 bvSize, std::stringstream &op1);

  std::string cfAdd(SymbolicElement *parent, std::stringstream &op1);
  std::string cfImul(SymbolicElement *parent, std::stringstream &op1);
  std::string cfMul(uint32 bvSize, std::stringstream &up);
  std::string cfNeg(uint32 bvSize, std::stringstream &op1);
  std::string cfRol(SymbolicElement *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op2);
  std::string cfRor(SymbolicElement *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op2);
  std::string cfSar(SymbolicElement *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op1, std::stringstream &op2);
  std::string cfShl(SymbolicElement *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op1, std::stringstream &op2);
  std::string cfShr(SymbolicElement *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op1, std::stringstream &op2);
  std::string cfSub(std::stringstream &op1, std::stringstream &op2);

  std::string clearFlag(void);

  std::string ofAdd(SymbolicElement *parent, uint32 extractSize, std::stringstream &op1, std::stringstream &op2);
  std::string ofImul(SymbolicElement *parent, std::stringstream &op1);
  std::string ofMul(uint32 bvSize, std::stringstream &up);
  std::string ofNeg(SymbolicElement *parent, uint32 bvSize, std::stringstream &op1);
  std::string ofRol(SymbolicElement *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op2);
  std::string ofRor(SymbolicElement *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op2);
  std::string ofSar(SymbolicElement *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op2);
  std::string ofShl(SymbolicElement *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op1, std::stringstream &op2);
  std::string ofShr(SymbolicElement *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op1, std::stringstream &op2);
  std::string ofSub(SymbolicElement *parent, uint32 extractSize, std::stringstream &op1, std::stringstream &op2);

  std::string pf(SymbolicElement *parent);
  std::string pfShl(SymbolicElement *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op2);

  std::string setFlag(void);

  std::string sf(SymbolicElement *parent, uint32 extractSize);
  std::string sfShl(SymbolicElement *parent, AnalysisProcessor &ap, uint32 bvSize, uint32 extractSize, std::stringstream &op2);

  std::string zf(SymbolicElement *parent, uint32 bvSize);
  std::string zfShl(SymbolicElement *parent, AnalysisProcessor &ap, uint32 bvSize, std::stringstream &op2);
}


#endif     /* !__EFLAGSEXPRESSIONS_H__ */
