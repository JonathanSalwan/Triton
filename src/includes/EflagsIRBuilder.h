#ifndef _EFLAGSIRBUILDER_H_
#define _EFLAGSIRBUILDER_H_

#include "AnalysisProcessor.h"
#include "SymbolicElement.h"


class EflagsIRBuilder {

  public:
    EflagsIRBuilder();
    ~EflagsIRBuilder();

  protected:
//    SymbolicElement *af(SymbolicElement *parent, AnalysisProcessor &ap) const;
//    SymbolicElement *cf(SymbolicElement *parent, AnalysisProcessor &ap) const;
//    SymbolicElement *of(SymbolicElement *parent, AnalysisProcessor &ap) const;
//    SymbolicElement *pf(SymbolicElement *parent, AnalysisProcessor &ap) const;
//    SymbolicElement *sf(SymbolicElement *parent, AnalysisProcessor &ap) const;
    SymbolicElement *zf(SymbolicElement *parent, AnalysisProcessor &ap) const;

};

#endif // _EFLAGSIRBUILDER_H_

