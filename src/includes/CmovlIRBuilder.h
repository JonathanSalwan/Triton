#ifndef _CMOVLIRBUILDER_H_
#define _CMOVLIRBUILDER_H_

#include "BaseIRBuilder.h"
#include "Inst.h"
#include "TwoOperandsTemplate.h"


class CmovlIRBuilder: public BaseIRBuilder, public TwoOperandsTemplate  {
  public:
    CmovlIRBuilder(uint64_t address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(AnalysisProcessor &ap) const;

    // From TwoOperandsTemplate
    virtual void regImm(AnalysisProcessor &ap, Inst &inst) const;

    virtual void regReg(AnalysisProcessor &ap, Inst &inst) const;

    virtual void regMem(AnalysisProcessor &ap, Inst &inst) const;

    virtual void memImm(AnalysisProcessor &ap, Inst &inst) const;

    virtual void memReg(AnalysisProcessor &ap, Inst &inst) const;
};

#endif // _CMOVLIRBUILDER_H_
