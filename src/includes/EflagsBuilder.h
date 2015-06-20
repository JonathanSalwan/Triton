#ifndef EFLAGSBUILDER_H
#define EFLAGSBUILDER_H

#include "AnalysisProcessor.h"
#include "Inst.h"
#include "EflagsExpressions.h"
#include "SymbolicElement.h"


/* Retunrs the symbolic element already crafted */
namespace EflagsBuilder {

  SymbolicElement *af(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *afNeg(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op1);

  SymbolicElement *cfAdd(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, std::stringstream &op1);
  SymbolicElement *cfImul(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op1);
  SymbolicElement *cfMul(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &up);
  SymbolicElement *cfNeg(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op1);
  SymbolicElement *cfRol(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op2);
  SymbolicElement *cfRor(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op2);
  SymbolicElement *cfSar(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *cfShl(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *cfShr(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *cfSub(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, std::stringstream &op1, std::stringstream &op2);

  SymbolicElement *clearFlag(Inst &inst, AnalysisProcessor &ap, regID_t flag);
  SymbolicElement *clearFlag(Inst &inst, AnalysisProcessor &ap, regID_t flag, std::string comment);

  SymbolicElement *ofAdd(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *ofImul(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op1);
  SymbolicElement *ofMul(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &up);
  SymbolicElement *ofNeg(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op1);
  SymbolicElement *ofRol(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op2);
  SymbolicElement *ofRor(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op2);
  SymbolicElement *ofSar(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op2);
  SymbolicElement *ofShl(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *ofShr(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op1, std::stringstream &op2);
  SymbolicElement *ofSub(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op1, std::stringstream &op2);

  SymbolicElement *pf(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap);
  SymbolicElement *pfShl(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op2);

  SymbolicElement *setFlag(Inst &inst, AnalysisProcessor &ap, regID_t flag);
  SymbolicElement *setFlag(Inst &inst, AnalysisProcessor &ap, regID_t flag, std::string comment);

  SymbolicElement *sf(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize);
  SymbolicElement *sfShl(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op2);

  SymbolicElement *zf(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize);
  SymbolicElement *zfShl(Inst &inst, SymbolicElement *parent, AnalysisProcessor &ap, uint32 dstSize, std::stringstream &op2);
};

#endif // EFLAGSBUILDER_H

