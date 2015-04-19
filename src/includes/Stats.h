#ifndef   __STATISTICS_H__
#define   __STATISTICS_H__

#include <chrono>
#include <cstdint>

using namespace std::chrono;

class Stats {

  private:
    uint64_t numberOfBranchesTaken;
    uint64_t numberOfExpressions;
    uint64_t numberOfUnknownInstruction;

    high_resolution_clock::time_point start;
    high_resolution_clock::time_point end;

  public:
    Stats();
    ~Stats();

    void      incNumberOfBranchesTaken(void);
    void      incNumberOfExpressions(uint64_t val);
    void      incNumberOfExpressions(void);
    void      incNumberOfUnknownInstruction(void);

    uint64_t  getNumberOfBranchesTaken(void);
    uint64_t  getNumberOfExpressions(void);
    uint64_t  getTimeOfExecution(void);
    uint64_t  getNumberOfUnknownInstruction(void);
};

#endif     /* !__STATISTICS_H__ */
