/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef CLDIRBUILDER_H
#define CLDIRBUILDER_H

#include "BaseIRBuilder.h"
#include "EflagsBuilder.h"
#include "Inst.h"
#include "NoneOperandTemplate.h"


class CldIRBuilder: public BaseIRBuilder, public NoneOperandTemplate {

  public:
    CldIRBuilder(uint64 address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(AnalysisProcessor &ap) const;

    // From OneOperandTemplate
    virtual void none(AnalysisProcessor &ap, Inst &inst) const;
};

#endif // CLDIRBUILDER_H
