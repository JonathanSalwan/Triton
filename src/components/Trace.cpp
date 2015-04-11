#include <sstream>

#include <boost/format.hpp>

#include "Colors.h"
#include "Trace.h"


Trace::Trace()
{
}


Trace::~Trace()
{
}


/* Add an instruction in the trace */
void Trace::addInstruction(Inst *instruction)
{
  this->instructions.push_back(instruction);
}


/* Returns the instructions list in the trace */
std::list<Inst *> &Trace::getInstructions()
{
  return this->instructions;
}


void Trace::display(std::ostream &os)
{
  boost::format outputInstruction("[%1%] %|3t| %2% %|21t| %3% %|61t|");
  boost::format outputExpression("%|61t|");

  for (auto inst : this->instructions){
    uint64_t count = 0;
    if (inst != nullptr) {
      std::stringstream expr(""), colr(ENDC);

      for (auto se : inst->getSymbolicElements()){

        if (count == 0) expr << se->getExpression()->str();
        else            expr << std::endl << boost::format(outputExpression) << se->getExpression()->str();

        if (se->isTainted)
          colr.str(GREEN);

        count++;
      }

      os << colr.str()
         << boost::format(outputInstruction)
          % std::to_string(inst->getThreadID())
          % boost::io::group(std::hex, std::showbase, inst->getAddress())
          % inst->getDisassembly()
         << expr.str()
         << ENDC
         << std::endl;
    }
  }
}
