#ifndef _CMCIRBUILDER_H_
#define _CMCIRBUILDER_H_

#include "BaseIRBuilder.h"
#include "EflagsBuilder.h"
#include "Inst.h"
#include "NoneOperandTemplate.h"


class CmcIRBuilder: public BaseIRBuilder, public NoneOperandTemplate {

  public:
    CmcIRBuilder(uint64_t address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(AnalysisProcessor &ap) const;

    // From OneOperandTemplate
    virtual void none(AnalysisProcessor &ap, Inst &inst) const;
};

#endif // _CMCIRBUILDER_H_
