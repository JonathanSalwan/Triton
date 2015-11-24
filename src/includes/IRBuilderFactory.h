/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef IRBUILDERFACTORY_H
#define IRBUILDERFACTORY_H

#include <list>
#include "IRBuilder.h"


namespace IRBuilderFactory {

  /* Keep a list of irbuilders */
  extern std::list<IRBuilder *> irbuilders;

  /* Flush Pin's cache and remove all irbuilders */
  void        flushCache(void);

  /* Return an IR object corresponding to the given instruction. */
  IRBuilder   *createIRBuilder(INS ins);
  IRBuilder   *buildIR(sint32 opcode, __uint address, std::string disas);

}

#endif // IRBUILDERFACTORY_H
