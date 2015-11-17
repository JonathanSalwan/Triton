/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef SETZIRBUILDER_H
#define SETZIRBUILDER_H

#include "BaseIRBuilder.h"
#include "EflagsBuilder.h"
#include "Inst.h"
#include "OneOperandTemplate.h"


class SetzIRBuilder: public BaseIRBuilder, public OneOperandTemplate {

  public:
    SetzIRBuilder(reg_size address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(AnalysisProcessor &ap) const;

    // From OneOperandTemplate
    virtual void none(AnalysisProcessor &ap, Inst &inst) const;

    virtual void reg(AnalysisProcessor &ap, Inst &inst) const;

    virtual void imm(AnalysisProcessor &ap, Inst &inst) const;

    virtual void mem(AnalysisProcessor &ap, Inst &inst) const;
};

#endif // SETZIRBUILDER_H
#endif // LIGHT_VERSION

