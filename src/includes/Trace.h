#ifndef _TRACE_H_
#define _TRACE_H_

#include <stdint.h>

#include <list>

#include "BasicBlock.h"


/* Trace of a run */
class Trace {

  private:
    std::list<BasicBlock>   bbls;
    uint64_t                endPoint;
    uint64_t                entryPoint;

  public:
    Trace(uint64_t entry, uint64_t end);
    ~Trace();

    //const std::list<BasicBlock>   &getForks();;
    //std::string                   dump(); // TODO
    uint64_t                      getEndPoint();
    uint64_t                      getEntryPoint();
    void                          addBasicBlock(const BasicBlock &bbl);
};

#endif /* !_TRACE_H_ */

