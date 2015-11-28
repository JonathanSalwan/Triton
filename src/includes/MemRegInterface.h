/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef MEMREGINTERFACE_H
#define MEMREGINTERFACE_H

#include "TritonTypes.h"


/* Memory and Register interface */
class MemRegInterface {

  public:
    virtual ~MemRegInterface() {};
    virtual __uint getBitSize(void) const = 0;
    virtual __uint getSize(void) const = 0;
    virtual __uint getAbstractHigh(void) const = 0;
    virtual __uint getAbstractLow(void) const = 0;

};

#endif // MEMREGINTERFACE_H

