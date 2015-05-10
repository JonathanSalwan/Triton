#ifndef _CWDEIRBUILDER_H_
#define _CWDEIRBUILDER_H_

#include "BaseIRBuilder.h"
#include "EflagsBuilder.h"
#include "Inst.h"
#include "NoneOperandTemplate.h"


class CwdeIRBuilder: public BaseIRBuilder, public NoneOperandTemplate {

  public:
    CwdeIRBuilder(uint64_t address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(AnalysisProcessor &ap) const;

    // From OneOperandTemplate
    virtual void none(AnalysisProcessor &ap, Inst &inst) const;
};

#endif // _CWDEIRBUILDER_H_
