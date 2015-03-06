#ifndef _ONEOPERANDTEMPLATE_H_
#define _ONEOPERANDTEMPLATE_H_

#include <vector>

#include "AnalysisProcessor.h"
#include "ContextHandler.h"
#include "Inst.h"
#include "IRBuilder.h"


class OneOperandTemplate {
  public:
    virtual ~OneOperandTemplate() { }

    virtual void templateMethod(
        const ContextHandler &ctxH,
        AnalysisProcessor &ap,
        Inst &inst,
        const std::vector< std::tuple<IRBuilder::operand_t, uint64_t, uint32_t> > &operands,
        std::string instructionName) const;

  protected:
    // Primitives uses in the templateMethod, must be implemented by subclasses.

    virtual void reg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const = 0;

    virtual void imm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const = 0;

    virtual void mem(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const = 0;
};

#endif // _ONEOPERANDTEMPLATE_H_
