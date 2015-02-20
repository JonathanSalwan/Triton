#ifndef _EFLAGSBUILDER_H_
#define _EFLAGSBUILDER_H_

#include "AnalysisProcessor.h"
#include "SymbolicElement.h"


namespace EflagsBuilder {

//  SymbolicElement *af(SymbolicElement *parent, AnalysisProcessor &ap);
  SymbolicElement *cf(SymbolicElement *parent, AnalysisProcessor &ap, std::stringstream &op1);
//  SymbolicElement *of(SymbolicElement *parent, AnalysisProcessor &ap);
//  SymbolicElement *pf(SymbolicElement *parent, AnalysisProcessor &ap);
  SymbolicElement *sf(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize);
  SymbolicElement *zf(SymbolicElement *parent, AnalysisProcessor &ap);

};

#endif // _EFLAGSBUILDER_H_

