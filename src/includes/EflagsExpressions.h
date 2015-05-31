#ifndef   __EFLAGSEXPRESSIONS_H__
#define   __EFLAGSEXPRESSIONS_H__

#include "AnalysisProcessor.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


/* Retunrs the flag expression */
namespace EflagsExpressions {

  std::string af(SymbolicElement *parent, uint32_t bvSize, std::stringstream &op1, std::stringstream &op2);
  std::string afNeg(SymbolicElement *parent, uint32_t bvSize, std::stringstream &op1);

  std::string cfAdd(SymbolicElement *parent, std::stringstream &op1);
  std::string cfNeg(uint32_t bvSize, std::stringstream &op1);
  std::string cfShl(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t bvSize, std::stringstream &op1, std::stringstream &op2);
  std::string cfShr(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t bvSize, std::stringstream &op1, std::stringstream &op2);
  std::string cfSub(std::stringstream &op1, std::stringstream &op2);

  std::string clearFlag(void);

  std::string ofAdd(SymbolicElement *parent, uint32_t extractSize, std::stringstream &op1, std::stringstream &op2);
  std::string ofNeg(SymbolicElement *parent, uint32_t bvSize, std::stringstream &op1);
  std::string ofShl(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t bvSize, std::stringstream &op1);
  std::string ofShr(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t bvSize, std::stringstream &op1);
  std::string ofSub(SymbolicElement *parent, uint32_t extractSize, std::stringstream &op1, std::stringstream &op2);

  std::string pf(SymbolicElement *parent);
  std::string pfShl(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t bvSize, std::stringstream &op1);

  std::string setFlag(void);

  std::string sf(SymbolicElement *parent, uint32_t extractSize);
  std::string sfShl(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t bvSize, uint32_t extractSize, std::stringstream &op1);

  std::string zf(SymbolicElement *parent, uint32_t bvSize);
  std::string zfShl(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t bvSize, std::stringstream &op1);
}


#endif     /* !__EFLAGSEXPRESSIONS_H__ */
