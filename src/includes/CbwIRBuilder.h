#ifndef _CBWIRBUILDER_H_
#define _CBWIRBUILDER_H_

#include "BaseIRBuilder.h"
#include "EflagsBuilder.h"
#include "Inst.h"
#include "NoneOperandTemplate.h"


class CbwIRBuilder: public BaseIRBuilder, public NoneOperandTemplate {

  public:
    CbwIRBuilder(uint64_t address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(AnalysisProcessor &ap) const;

    // From OneOperandTemplate
    virtual void none(AnalysisProcessor &ap, Inst &inst) const;
};

#endif // _CBWIRBUILDER_H_
