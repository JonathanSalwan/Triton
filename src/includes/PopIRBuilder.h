#ifndef _POPIRBUILDER_H_
#define _POPIRBUILDER_H_

#include "BaseIRBuilder.h"
#include "EflagsBuilder.h"
#include "Inst.h"
#include "OneOperandTemplate.h"


class PopIRBuilder: public BaseIRBuilder, public OneOperandTemplate {

  public:
    PopIRBuilder(uint64_t address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(const ContextHandler &ctxH, AnalysisProcessor &ap) const;

    // From OneOperandTemplate
    virtual void none(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;

    virtual void reg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;

    virtual void imm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;

    virtual void mem(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;
};

#endif // _POPIRBUILDER_H_
