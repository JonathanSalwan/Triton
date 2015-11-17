/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef CMOVSIRBUILDER_H
#define CMOVSIRBUILDER_H

#include "BaseIRBuilder.h"
#include "Inst.h"
#include "TwoOperandsTemplate.h"


class CmovsIRBuilder: public BaseIRBuilder, public TwoOperandsTemplate  {
  public:
    CmovsIRBuilder(reg_size address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(AnalysisProcessor &ap) const;

    // From TwoOperandsTemplate
    virtual void regImm(AnalysisProcessor &ap, Inst &inst) const;

    virtual void regReg(AnalysisProcessor &ap, Inst &inst) const;

    virtual void regMem(AnalysisProcessor &ap, Inst &inst) const;

    virtual void memImm(AnalysisProcessor &ap, Inst &inst) const;

    virtual void memReg(AnalysisProcessor &ap, Inst &inst) const;
};

#endif // CMOVSIRBUILDER_H
#endif // LIGHT_VERSION

