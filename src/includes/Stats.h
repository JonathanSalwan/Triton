#ifndef   __STATISTICS_H__
#define   __STATISTICS_H__

#include <chrono>
#include <cstdint>

using namespace std::chrono;

class Stats {

  private:
    uint64_t numberOfExpressions;
    uint64_t numberOfUnknownInstruction;
    uint64_t numberOfBranchesTaken;
    uint64_t timeOfExecution;
    uint64_t codeCoverage;

    high_resolution_clock::time_point start;
    high_resolution_clock::time_point end;

  public:
    Stats();
    ~Stats();

    void display(void);
    void incNumberOfExpressions(void);
    void incNumberOfExpressions(uint64_t val);
    void incNumberOfUnknownInstruction(void);
    void incNumberOfBranchesTaken(void);
};

#endif     /* !__STATISTICS_H__ */
