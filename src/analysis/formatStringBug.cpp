
#include "Triton.h"
#include "analysis/FormatString.h"


void formatStringBugAnalysis(unsigned long insAddr, unsigned long rdi)
{
  std::string content = std::string((const char *)rdi);
  std::stringstream str;

  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  /* In 64-bit, RDI holds the first argument.
   * If this argument is tainted, it's probably vulnerable */
  if (trace->taintEngine->isMemoryTainted(rdi)){
    str << "[call::printf] RDI content is tainted: " << content;
    displayBug(str.str());
    str.str("[call::printf] This printf is probably vulnerable");
    displayBug(str.str());
  }
}


