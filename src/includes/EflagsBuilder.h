#ifndef _EFLAGSBUILDER_H_
#define _EFLAGSBUILDER_H_

#include "AnalysisProcessor.h"
#include "SymbolicElement.h"


namespace EflagsBuilder {
  SymbolicElement *af(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *afNeg(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1);
  SymbolicElement *cfAdd(SymbolicElement *parent, AnalysisProcessor &ap, std::stringstream &op1);
  SymbolicElement *cfNeg(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1);
  SymbolicElement *cfSub(SymbolicElement *parent, AnalysisProcessor &ap, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *clearFlag(AnalysisProcessor &ap, regID_t flag);
  SymbolicElement *clearFlag(AnalysisProcessor &ap, regID_t flag, std::string comment);
  SymbolicElement *ofAdd(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *ofNeg(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1);
  SymbolicElement *ofSub(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *pf(SymbolicElement *parent, AnalysisProcessor &ap);
  SymbolicElement *setFlag(AnalysisProcessor &ap, regID_t flag);
  SymbolicElement *setFlag(AnalysisProcessor &ap, regID_t flag, std::string comment);
  SymbolicElement *sf(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize);
  SymbolicElement *zf(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize);
};

#endif // _EFLAGSBUILDER_H_

