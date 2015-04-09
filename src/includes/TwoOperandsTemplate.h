#ifndef _TWOOPERANDSTEMPLATE_H_
#define _TWOOPERANDSTEMPLATE_H_

#include <vector>

#include "AnalysisProcessor.h"
#include "ContextHandler.h"
#include "Inst.h"
#include "IRBuilder.h"
#include "OperandTemplate.h"


class TwoOperandsTemplate: public OperandTemplate {
  public:
    virtual ~TwoOperandsTemplate() { }

    virtual void templateMethod(
        const ContextHandler &ctxH,
        AnalysisProcessor &ap,
        Inst &inst,
        const std::vector< std::tuple<IRBuilderOperand::operand_t, uint64_t, uint32_t> > &operands,
        std::string instructionName) const;

  protected:
    // Primitives uses in the templateMethod, must be implemented by subclasses.

    virtual void regImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const = 0;

    virtual void regReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const = 0;

    virtual void regMem(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const = 0;

    virtual void memImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const = 0;

    virtual void memReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const = 0;
};

#endif // _TWOOPERANDSTEMPLATE_H_
