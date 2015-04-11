#ifndef _MOVIRBUILDER_H_
#define _MOVIRBUILDER_H_

#include "BaseIRBuilder.h"
#include "Inst.h"
#include "TwoOperandsTemplate.h"


class MovIRBuilder: public BaseIRBuilder, public TwoOperandsTemplate  {
  public:
    MovIRBuilder(uint64_t address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(AnalysisProcessor &ap) const;

    // From TwoOperandsTemplate
    virtual void regImm(AnalysisProcessor &ap, Inst &inst) const;

    virtual void regReg(AnalysisProcessor &ap, Inst &inst) const;

    virtual void regMem(AnalysisProcessor &ap, Inst &inst) const;

    virtual void memImm(AnalysisProcessor &ap, Inst &inst) const;

    virtual void memReg(AnalysisProcessor &ap, Inst &inst) const;

  protected:
    // Store a pointer to function building the bit vector expression.
    // Truly useful for subclasses.
    std::string (*extender) (std::string, uint64_t);
};

#endif // _MOVIRBUILDER_H_
