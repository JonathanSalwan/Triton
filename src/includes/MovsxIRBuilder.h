#ifndef _MOVSXIRBUILDER_H_
#define _MOVSXIRBUILDER_H_

#include "MovIRBuilder.h"


class MovsxIRBuilder: public MovIRBuilder {
  public:
    MovsxIRBuilder(uint64_t address, const std::string &disassembly);
};

#endif // _MOVSXIRBUILDER_H_
