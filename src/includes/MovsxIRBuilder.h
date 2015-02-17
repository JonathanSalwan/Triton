#ifndef _MOVSXIRBUILDER_H_
#define _MOVSXIRBUILDER_H_

#include "MovIRBuilder.h"


class MovsxIRBuilder: public MovIRBuilder {
  public:
    MovsxIRBuilder(uint64_t address, const std::string &disassembly);


    // Movsx can't handle these configurations of operands.
    // Throws a runtime error.
    void regImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;
    void memImm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;
    void memReg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const;
};

#endif // _MOVSXIRBUILDER_H_
