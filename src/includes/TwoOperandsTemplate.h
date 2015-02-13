#ifndef _TWOOPERANDSTEMPLATE_H_
#define _TWOOPERANDSTEMPLATE_H_

#include <sstream>
#include <vector>

#include "ContextHandler.h"
#include "IRBuilder.h"


class TwoOperandsTemplate {
  public:
    virtual ~TwoOperandsTemplate() { }

    virtual std::stringstream *templateMethod(
        const ContextHandler &ctxH,
        const std::vector< std::tuple<IRBuilder::operand_t, uint64_t, uint32_t> > &operands,
        std::string instructionName) const;

  protected:
    // Primitives uses in the templateMethod, must be implemented by subclasses.

    virtual std::stringstream *regImm(const ContextHandler &ctxH) const = 0;

    virtual std::stringstream *regReg(const ContextHandler &ctxH) const = 0;

    virtual std::stringstream *regMem(const ContextHandler &ctxH) const = 0;

    virtual std::stringstream *memImm(const ContextHandler &ctxH) const = 0;

    virtual std::stringstream *memReg(const ContextHandler &ctxH) const = 0;
};

#endif // _TWOOPERANDSTEMPLATE_H_
