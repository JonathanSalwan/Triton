/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef DIRECTOR_H
#define DIRECTOR_H

#include "IRBuilder.h"


// Return an IR object corresponding to the given instruction.
IRBuilder *createIRBuilder(INS ins);

#endif // DIRECTOR_H
