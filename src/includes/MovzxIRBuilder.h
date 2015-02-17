#ifndef _MOVZXIRBUILDER_H_
#define _MOVZXIRBUILDER_H_

#include "MovIRBuilder.h"


class MovzxIRBuilder: public MovIRBuilder {
  public:
    MovzxIRBuilder(uint64_t address, const std::string &disassembly);

    // Movzx can't handle these configurations of operands.
    // Throws a runtime error.
    void regImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;
    void memImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;
    void memReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;
};

#endif // _MOVZXIRBUILDER_H_
