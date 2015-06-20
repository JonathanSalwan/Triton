#include <sstream>
#include <fstream>

#include <boost/format.hpp>

#include <Colors.h>
#include <Trace.h>


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


/* Returns the last instuction added */
Inst *Trace::getLastInstruction(void)
{
  return this->instructions.back();
}


/* Returns the instructions list in the trace */
std::list<Inst *> &Trace::getInstructions()
{
  return this->instructions;
}


void Trace::save(std::stringstream &file)
{
  std::ofstream f;
  f.open (file.str().c_str());

  boost::format outputInstruction("[%1%] %|3t| %2% %|21t| %3% %|61t|");
  boost::format outputExpression("%|61t|");

  for (auto inst : this->instructions){
    uint64 count = 0;
    if (inst != nullptr) {
      std::stringstream expr(""), colr(ENDC);

      for (auto se : inst->getSymbolicElements()){

        if (se->isTainted)
          colr.str(GREEN);

        if (count == 0) expr << colr.str() << se->getExpression()->str() << ENDC;
        else            expr << std::endl << colr.str() << boost::format(outputExpression) << se->getExpression()->str() << ENDC;

        count++;
      }

      f << colr.str()
        << boost::format(outputInstruction)
         % std::to_string(inst->getThreadID())
         % boost::io::group(std::hex, std::showbase, inst->getAddress())
         % inst->getDisassembly()
        << expr.str()
        << ENDC
        << std::endl;
    }
  }
  f.close();
}

