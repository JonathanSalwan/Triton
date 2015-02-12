#ifndef _DIRECTOR_H_
#define _DIRECTOR_H_

#include "IRBuilder.h"


// Return an IR object corresponding to the given instruction.
IRBuilder *createIRBuilder(INS ins);

#endif // _DIRECTOR_H_
