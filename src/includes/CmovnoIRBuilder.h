#ifndef _CMOVNOIRBUILDER_H_
#define _CMOVNOIRBUILDER_H_

#include "BaseIRBuilder.h"
#include "Inst.h"
#include "TwoOperandsTemplate.h"


class CmovnoIRBuilder: public BaseIRBuilder, public TwoOperandsTemplate  {
  public:
    CmovnoIRBuilder(uint64_t address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(AnalysisProcessor &ap) const;

    // From TwoOperandsTemplate
    virtual void regImm(AnalysisProcessor &ap, Inst &inst) const;

    virtual void regReg(AnalysisProcessor &ap, Inst &inst) const;

    virtual void regMem(AnalysisProcessor &ap, Inst &inst) const;

    virtual void memImm(AnalysisProcessor &ap, Inst &inst) const;

    virtual void memReg(AnalysisProcessor &ap, Inst &inst) const;
};

#endif // _CMOVNOIRBUILDER_H_
