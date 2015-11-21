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


void Stats::incNumberOfExpressions(__uint val) {
  this->numberOfExpressions += val;
}


void Stats::incNumberOfUnknownInstruction(void) {
  this->numberOfUnknownInstruction++;
}


void Stats::incNumberOfBranchesTaken(void) {
  this->numberOfBranchesTaken++;
}


__uint  Stats::getNumberOfBranchesTaken(void) {
  return this->numberOfBranchesTaken;
}


__uint  Stats::getNumberOfExpressions(void) {
  return this->numberOfExpressions;
}


__uint  Stats::getNumberOfUnknownInstruction(void) {
  return this->numberOfUnknownInstruction;
}


__uint  Stats::getTimeOfExecution(void) {
  this->end = high_resolution_clock::now();
  __uint timeOfExecution = std::chrono::duration_cast<std::chrono::seconds>(this->end - this->start).count();
  return timeOfExecution;
}

#endif /* LIGHT_VERSION */

