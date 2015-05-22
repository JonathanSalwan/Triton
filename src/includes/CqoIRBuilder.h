#ifndef _CQOIRBUILDER_H_
#define _CQOIRBUILDER_H_

#include "BaseIRBuilder.h"
#include "EflagsBuilder.h"
#include "Inst.h"
#include "NoneOperandTemplate.h"


class CqoIRBuilder: public BaseIRBuilder, public NoneOperandTemplate {

  public:
    CqoIRBuilder(uint64_t address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(AnalysisProcessor &ap) const;

    // From OneOperandTemplate
    virtual void none(AnalysisProcessor &ap, Inst &inst) const;
};

#endif // _CQOIRBUILDER_H_
