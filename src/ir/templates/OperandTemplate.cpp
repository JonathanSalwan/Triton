#include <OperandTemplate.h>

void OperandTemplate::stop(std::string disass)
{
  throw std::runtime_error("Error: \""
                         + disass
                         + "\" is an invalid instruction. Wrong kind of operands.");
}
