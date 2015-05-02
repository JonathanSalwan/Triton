#ifndef _CLDIRBUILDER_H_
#define _CLDIRBUILDER_H_

#include "BaseIRBuilder.h"
#include "EflagsBuilder.h"
#include "Inst.h"
#include "NoneOperandTemplate.h"


class CldIRBuilder: public BaseIRBuilder, public NoneOperandTemplate {

  public:
    CldIRBuilder(uint64_t address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(AnalysisProcessor &ap) const;

    // From OneOperandTemplate
    virtual void none(AnalysisProcessor &ap, Inst &inst) const;
};

#endif // _CLDIRBUILDER_H_
