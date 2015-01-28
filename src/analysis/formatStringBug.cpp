
#include "Triton.h"
#include "analysis/formatString.h"


void formatStringBugAnalysis(unsigned long rdi)
{
  list<UINT64>::iterator i;
  std::string content = std::string((const char *)rdi);
  std::stringstream str;

  if (taintEngine->isMemoryTainted(rdi)){
    if (content.find("%s") == string::npos){
      str << "[call::printf] RDI content is tainted: " << content;
      displayBug(str.str());
      str.str("[call::printf] This printf is probably vulnerable");
      displayBug(str.str());
    }
  }
}


