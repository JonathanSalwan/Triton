#ifndef _MOVIRBUILDER_H_
#define _MOVIRBUILDER_H_

#include "BaseIRBuilder.h"
#include "Inst.h"
#include "TwoOperandsTemplate.h"


class MovIRBuilder: public BaseIRBuilder, public TwoOperandsTemplate  {
  public:
    MovIRBuilder(uint64_t address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(const ContextHandler &ctxH, AnalysisProcessor &ap) const;

    // From TwoOperandsTemplate
    virtual void regImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;

    virtual void regReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;

    virtual void regMem(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;

    virtual void memImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;

    virtual void memReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;

};

#endif // _MOVIRBUILDER_H_
