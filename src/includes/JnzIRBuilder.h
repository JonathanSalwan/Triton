/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef JNZIRBUILDER_H
#define JNZIRBUILDER_H

#include "BaseIRBuilder.h"
#include "EflagsBuilder.h"
#include "Inst.h"
#include "OneOperandTemplate.h"


class JnzIRBuilder: public BaseIRBuilder, public OneOperandTemplate {

  public:
    JnzIRBuilder(reg_size address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(AnalysisProcessor &ap) const;

    // From OneOperandTemplate
    virtual void none(AnalysisProcessor &ap, Inst &inst) const;

    virtual void reg(AnalysisProcessor &ap, Inst &inst) const;

    virtual void imm(AnalysisProcessor &ap, Inst &inst) const;

    virtual void mem(AnalysisProcessor &ap, Inst &inst) const;
};

#endif // JNZIRBUILDER_H
#endif // LIGHT_VERSION

