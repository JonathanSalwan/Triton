/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_PINUTILS_H
#define TRITON_PINUTILS_H

#include <list>
#include <string>
#include <pin.H>
#include "TritonTypes.h"


__uint      getBaseAddress(__uint address);
__uint      getInsOffset(__uint address);
std::string getImageName(__uint address);


#endif /* ! _PINUTIL_H_ */

