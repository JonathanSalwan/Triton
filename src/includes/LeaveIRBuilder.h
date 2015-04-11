#ifndef _LEAVEIRBUILDER_H_
#define _LEAVEIRBUILDER_H_

#include "BaseIRBuilder.h"
#include "EflagsBuilder.h"
#include "Inst.h"
#include "NoneOperandTemplate.h"


class LeaveIRBuilder: public BaseIRBuilder, public NoneOperandTemplate {

  public:
    LeaveIRBuilder(uint64_t address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(AnalysisProcessor &ap) const;

    // From OneOperandTemplate
    virtual void none(AnalysisProcessor &ap, Inst &inst) const;
};

#endif // _LEAVEIRBUILDER_H_
