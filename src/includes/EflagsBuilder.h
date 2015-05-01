#ifndef _EFLAGSBUILDER_H_
#define _EFLAGSBUILDER_H_

#include "AnalysisProcessor.h"
#include "SymbolicElement.h"


namespace EflagsBuilder {
  SymbolicElement *af(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *cfAdd(SymbolicElement *parent, AnalysisProcessor &ap, std::stringstream &op1);
  SymbolicElement *cfSub(SymbolicElement *parent, AnalysisProcessor &ap, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *clearFlag(AnalysisProcessor &ap, regID_t flag);
  SymbolicElement *ofAdd(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *ofSub(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *pf(SymbolicElement *parent, AnalysisProcessor &ap);
  SymbolicElement *setFlag(AnalysisProcessor &ap, regID_t flag);
  SymbolicElement *sf(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize);
  SymbolicElement *zf(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize);
};

#endif // _EFLAGSBUILDER_H_

