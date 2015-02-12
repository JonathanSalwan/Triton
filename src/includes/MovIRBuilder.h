#ifndef _MOVIRBUILDER_H_
#define _MOVIRBUILDER_H_

#include "BaseIRBuilder.h"
#include "TwoOperandsTemplate.h"


class MovIRBuilder: public BaseIRBuilder, public TwoOperandsTemplate  {
  public:
    MovIRBuilder(uint64_t address, const std::string &disassembly);

    // From BaseIRBuilder
    virtual std::stringstream *process(const ContextHandler &ctxH) const;

    // From TwoOperandsTemplate
    virtual std::stringstream *regImm(const ContextHandler &ctxH) const;

    virtual std::stringstream *regReg(const ContextHandler &ctxH) const;

    virtual std::stringstream *regMem(const ContextHandler &ctxH) const;

    virtual std::stringstream *memImm(const ContextHandler &ctxH) const;

    virtual std::stringstream *memReg(const ContextHandler &ctxH) const;

};

#endif // _MOVIRBUILDER_H_
