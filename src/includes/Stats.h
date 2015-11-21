/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef STATISTICS_H
#define STATISTICS_H

#include <chrono>
#include "TritonTypes.h"

using namespace std::chrono;

class Stats {

  private:
    __uint numberOfBranchesTaken;
    __uint numberOfExpressions;
    __uint numberOfUnknownInstruction;

    high_resolution_clock::time_point start;
    high_resolution_clock::time_point end;

  public:
    Stats();
    ~Stats();

    void    incNumberOfBranchesTaken(void);
    void    incNumberOfExpressions(__uint val);
    void    incNumberOfExpressions(void);
    void    incNumberOfUnknownInstruction(void);

    __uint  getNumberOfBranchesTaken(void);
    __uint  getNumberOfExpressions(void);
    __uint  getTimeOfExecution(void);
    __uint  getNumberOfUnknownInstruction(void);
};

#endif /* !__STATISTICS_H__ */
#endif /* LIGHT_VERSION */

