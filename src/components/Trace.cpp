#include <sstream>

#include <boost/format.hpp>

#include "Colors.h"
#include "Trace.h"


Trace::Trace(): symbolicEngine()
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
  boost::format outputInstruction("%1% %|15t| %2% %|55t|");

  for (auto inst : this->instructions){
    uint64_t count = 0;
    if (inst != nullptr) {
      std::stringstream expr(""), colr(ENDC);

      for (auto se : inst->getSymbolicElements()){

        if (count == 0) expr << se->getExpression()->str();
        else            expr << std::endl << boost::format(outputInstruction) % "" % "" << se->getExpression()->str();

        if (se->isTainted)
          colr.str(GREEN);

        count++;
      }

      os << colr.str()
         << boost::format(outputInstruction)
          % boost::io::group(std::hex, std::showbase, inst->getAddress())
          % inst->getDisassembly()
         << expr.str()
         << ENDC
         << std::endl;
    }
  }
}
