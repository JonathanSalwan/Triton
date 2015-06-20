#ifndef   STATISTICS_H
#define   STATISTICS_H

#include <chrono>
#include "TritonTypes.h"

using namespace std::chrono;

class Stats {

  private:
    uint64 numberOfBranchesTaken;
    uint64 numberOfExpressions;
    uint64 numberOfUnknownInstruction;

    high_resolution_clock::time_point start;
    high_resolution_clock::time_point end;

  public:
    Stats();
    ~Stats();

    void    incNumberOfBranchesTaken(void);
    void    incNumberOfExpressions(uint64 val);
    void    incNumberOfExpressions(void);
    void    incNumberOfUnknownInstruction(void);

    uint64  getNumberOfBranchesTaken(void);
    uint64  getNumberOfExpressions(void);
    uint64  getTimeOfExecution(void);
    uint64  getNumberOfUnknownInstruction(void);
};

#endif     /* !__STATISTICS_H__ */
