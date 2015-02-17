#ifndef _EFLAGSBUILDER_H_
#define _EFLAGSBUILDER_H_

#include "AnalysisProcessor.h"
#include "SymbolicElement.h"


namespace EflagsBuilder {

//    SymbolicElement *af(SymbolicElement *parent, AnalysisProcessor &ap);
//    SymbolicElement *cf(SymbolicElement *parent, AnalysisProcessor &ap);
//    SymbolicElement *of(SymbolicElement *parent, AnalysisProcessor &ap);
//    SymbolicElement *pf(SymbolicElement *parent, AnalysisProcessor &ap);
//    SymbolicElement *sf(SymbolicElement *parent, AnalysisProcessor &ap);
  SymbolicElement *zf(SymbolicElement *parent, AnalysisProcessor &ap);

};

#endif // _EFLAGSBUILDER_H_

