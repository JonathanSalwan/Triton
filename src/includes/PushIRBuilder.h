#ifndef _PUSHIRBUILDER_H_
#define _PUSHIRBUILDER_H_

#include "BaseIRBuilder.h"
#include "EflagsBuilder.h"
#include "Inst.h"
#include "OneOperandTemplate.h"


class PushIRBuilder: public BaseIRBuilder, public OneOperandTemplate {

  public:
    PushIRBuilder(uint64_t address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(const ContextHandler &ctxH, AnalysisProcessor &ap) const;

    // From OneOperandTemplate
    virtual void reg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;

    virtual void imm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;

    virtual void mem(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;
};

#endif // _PUSHIRBUILDER_H_
