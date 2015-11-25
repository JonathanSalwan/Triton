/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef CDQEIRBUILDER_H
#define CDQEIRBUILDER_H

#include "BaseIRBuilder.h"
#include "EflagsBuilder.h"
#include "Inst.h"
#include "NoneOperandTemplate.h"


class CdqeIRBuilder: public BaseIRBuilder, public NoneOperandTemplate {

  public:
    CdqeIRBuilder(__uint address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(void) const;

    // From OneOperandTemplate
    virtual void none(Inst &inst) const;
};

#endif // CDQEIRBUILDER_H
#endif // LIGHT_VERSION

