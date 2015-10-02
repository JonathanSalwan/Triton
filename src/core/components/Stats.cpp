/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <Stats.h>
#include <Colors.h>



Stats::Stats() {
  this->numberOfExpressions         = 0;
  this->numberOfUnknownInstruction  = 0;
  this->numberOfBranchesTaken       = 0;

  this->start = high_resolution_clock::now();
}


Stats::~Stats() {
}


void Stats::incNumberOfExpressions(void) {
  this->numberOfExpressions++;
}


void Stats::incNumberOfExpressions(uint64 val) {
  this->numberOfExpressions += val;
}


void Stats::incNumberOfUnknownInstruction(void) {
  this->numberOfUnknownInstruction++;
}


void Stats::incNumberOfBranchesTaken(void) {
  this->numberOfBranchesTaken++;
}


uint64  Stats::getNumberOfBranchesTaken(void) {
  return this->numberOfBranchesTaken;
}


uint64  Stats::getNumberOfExpressions(void) {
  return this->numberOfExpressions;
}


uint64  Stats::getNumberOfUnknownInstruction(void) {
  return this->numberOfUnknownInstruction;
}


uint64  Stats::getTimeOfExecution(void) {
  this->end = high_resolution_clock::now();
  uint64 timeOfExecution = std::chrono::duration_cast<std::chrono::seconds>(this->end - this->start).count();
  return timeOfExecution;
}

#endif /* LIGHT_VERSION */

