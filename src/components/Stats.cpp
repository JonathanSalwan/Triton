
#include <boost/format.hpp>

#include <Stats.h>
#include <Colors.h>



Stats::Stats()
{
  this->numberOfExpressions         = 0;
  this->numberOfUnknownInstruction  = 0;
  this->numberOfBranchesTaken       = 0;

  this->start = high_resolution_clock::now();
}


Stats::~Stats()
{
}


void Stats::incNumberOfExpressions(void)
{
  this->numberOfExpressions++;
}


void Stats::incNumberOfExpressions(uint64_t val)
{
  this->numberOfExpressions += val;
}


void Stats::incNumberOfUnknownInstruction(void)
{
  this->numberOfUnknownInstruction++;
}


void Stats::incNumberOfBranchesTaken(void)
{
  this->numberOfBranchesTaken++;
}


uint64_t  Stats::getNumberOfBranchesTaken(void)
{
  return this->numberOfBranchesTaken;
}


uint64_t  Stats::getNumberOfExpressions(void)
{
  return this->numberOfExpressions;
}


uint64_t  Stats::getNumberOfUnknownInstruction(void)
{
  return this->numberOfUnknownInstruction;
}


uint64_t  Stats::getTimeOfExecution(void)
{
  this->end = high_resolution_clock::now();
  uint64_t timeOfExecution = std::chrono::duration_cast<std::chrono::seconds>(this->end - this->start).count();
  return timeOfExecution;
}

