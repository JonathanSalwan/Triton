/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef LEAVEIRBUILDER_H
#define LEAVEIRBUILDER_H

#include "BaseIRBuilder.h"
#include "EflagsBuilder.h"
#include "Inst.h"
#include "NoneOperandTemplate.h"


class LeaveIRBuilder: public BaseIRBuilder, public NoneOperandTemplate {

  public:
    LeaveIRBuilder(__uint address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual Inst *process(void) const;

    // From OneOperandTemplate
    virtual void none(Inst &inst) const;
};

#endif // LEAVEIRBUILDER_H
#endif // LIGHT_VERSION

