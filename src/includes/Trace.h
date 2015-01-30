#ifndef _TRACE_H_
#define _TRACE_H_

#include <stdint.h>

#include <list>

#include "BasicBlock.h"


/* Trace of a run */
class Trace {
  private:
    uint64_t entryPoint;
    uint64_t endPoint;
    std::list<BBL> bbls;

  public:
    Trace(uint64_t entry, uint64_t end) : entryPoint(entry), endPoint(end), bbls() { }
    ~Trace();

    uint64_t getEntryPoint() { return entryPoint; }
    uint64_t getEndPoint() { return endPoint; }


    std::string dump();

    void addBBL(const BBL &bbl);
    const std::list<BBL> &getForks();;
};

#endif /* !_TRACE_H_ */
