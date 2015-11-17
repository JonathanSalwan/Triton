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
    reg_size numberOfBranchesTaken;
    reg_size numberOfExpressions;
    reg_size numberOfUnknownInstruction;

    high_resolution_clock::time_point start;
    high_resolution_clock::time_point end;

  public:
    Stats();
    ~Stats();

    void    incNumberOfBranchesTaken(void);
    void    incNumberOfExpressions(reg_size val);
    void    incNumberOfExpressions(void);
    void    incNumberOfUnknownInstruction(void);

    reg_size  getNumberOfBranchesTaken(void);
    reg_size  getNumberOfExpressions(void);
    reg_size  getTimeOfExecution(void);
    reg_size  getNumberOfUnknownInstruction(void);
};

#endif /* !__STATISTICS_H__ */
#endif /* LIGHT_VERSION */

