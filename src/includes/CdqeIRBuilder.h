#ifndef _CDQEIRBUILDER_H_
#define _CDQEIRBUILDER_H_

#include "BaseIRBuilder.h"
#include "EflagsBuilder.h"
#include "Inst.h"
#include "NoneOperandTemplate.h"


class CdqeIRBuilder: public BaseIRBuilder, public NoneOperandTemplate {

  public:
    CdqeIRBuilder(uint64_t address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(AnalysisProcessor &ap) const;

    // From OneOperandTemplate
    virtual void none(AnalysisProcessor &ap, Inst &inst) const;
};

#endif // _CDQEIRBUILDER_H_
