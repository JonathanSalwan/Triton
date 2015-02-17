#ifndef _MOVZXIRBUILDER_H_
#define _MOVZXIRBUILDER_H_

#include "MovIRBuilder.h"


class MovzxIRBuilder: public MovIRBuilder {
  public:
    MovzxIRBuilder(uint64_t address, const std::string &disassembly);
};

#endif // _MOVZXIRBUILDER_H_
