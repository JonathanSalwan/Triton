#ifndef _EFLAGSBUILDER_H_
#define _EFLAGSBUILDER_H_

#include "AnalysisProcessor.h"
#include "Inst.h"
#include "EflagsExpressions.h"
#include "SymbolicElement.h"


/* Retunrs the symbolic element already crafted */
namespace EflagsBuilder {

  SymbolicElement *af(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *afNeg(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1);

  SymbolicElement *cfAdd(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, std::stringstream &op1);
  SymbolicElement *cfNeg(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1);
  SymbolicElement *cfShl(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *cfSub(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, std::stringstream &op1, std::stringstream &op2);

  SymbolicElement *clearFlag(Inst &inst, AnalysisProcessor &ap, regID_t flag);
  SymbolicElement *clearFlag(Inst &inst, AnalysisProcessor &ap, regID_t flag, std::string comment);

  SymbolicElement *ofAdd(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *ofNeg(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1);
  SymbolicElement *ofShl(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1);
  SymbolicElement *ofSub(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1, std::stringstream &op2);

  SymbolicElement *pf(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap);
  SymbolicElement *pfShl(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1);

  SymbolicElement *setFlag(Inst &inst, AnalysisProcessor &ap, regID_t flag);
  SymbolicElement *setFlag(Inst &inst, AnalysisProcessor &ap, regID_t flag, std::string comment);

  SymbolicElement *sf(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize);
  SymbolicElement *sfShl(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1);

  SymbolicElement *zf(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize);
  SymbolicElement *zfShl(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize, std::stringstream &op1);
};

#endif // _EFLAGSBUILDER_H_

