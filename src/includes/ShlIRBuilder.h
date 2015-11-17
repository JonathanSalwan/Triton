/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef SHLIRBUILDER_H
#define SHLIRBUILDER_H

#include "BaseIRBuilder.h"
#include "EflagsBuilder.h"
#include "Inst.h"
#include "TwoOperandsTemplate.h"


class ShlIRBuilder: public BaseIRBuilder, public TwoOperandsTemplate {

  public:
    ShlIRBuilder(reg_size address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(AnalysisProcessor &ap) const;

    // From TwoOperandsTemplate
    virtual void regImm(AnalysisProcessor &ap, Inst &inst) const;

    virtual void regReg(AnalysisProcessor &ap, Inst &inst) const;

    virtual void regMem(AnalysisProcessor &ap, Inst &inst) const;

    virtual void memImm(AnalysisProcessor &ap, Inst &inst) const;

    virtual void memReg(AnalysisProcessor &ap, Inst &inst) const;
};

#endif // SHLIRBUILDER_H
#endif // LIGHT_VERSION

