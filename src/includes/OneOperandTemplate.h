#ifndef _ONEOPERANDTEMPLATE_H_
#define _ONEOPERANDTEMPLATE_H_

#include <vector>

#include "AnalysisProcessor.h"
#include "ContextHandler.h"
#include "Inst.h"
#include "IRBuilder.h"
#include "OperandTemplate.h"


class OneOperandTemplate: public OperandTemplate {
  public:
    virtual ~OneOperandTemplate() { }

    virtual void templateMethod(
        AnalysisProcessor &ap,
        Inst &inst,
        const std::vector< std::tuple<IRBuilderOperand::operand_t, uint64_t, uint32_t> > &operands,
        std::string instructionName) const;

  protected:
    // Primitives uses in the templateMethod, must be implemented by subclasses.

    virtual void none(AnalysisProcessor &ap, Inst &inst) const = 0;

    virtual void reg(AnalysisProcessor &ap, Inst &inst) const = 0;

    virtual void imm(AnalysisProcessor &ap, Inst &inst) const = 0;

    virtual void mem(AnalysisProcessor &ap, Inst &inst) const = 0;
};

#endif // _ONEOPERANDTEMPLATE_H_
