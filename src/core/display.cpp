
#include "pin.H"
#include "Triton.h"


#define _BLUE   "\033[94m"
#define _GREEN  "\033[92m"
#define _YELLOW "\033[93m"
#define _RED    "\033[91m"
#define _ENDC   "\033[0m"

/* Output format */
boost::format outputInstruction("%1% %|15t| %2% %|55t| %3%\n");


/* Function used in each instruction callback to display the trace */
VOID displayTrace(ADDRINT addr, const std::string &insDis, symbolicElement *symElement)
{
  std::stringstream addrFormat;
  std::stringstream taintColor;

  /* Sometime, the address must not be display */
  if (addr != 0)
    addrFormat << boost::io::group(hex, showbase, addr);

  /* If taint is enable, the trace is colord */
  if (symElement->isTainted)
    taintColor << _GREEN;

  /* Display */
  std::cout << taintColor.str() << boost::format(outputInstruction) % addrFormat.str() % insDis % symElement->getExpression() << _ENDC;
}


/* Currently, only used in src/ir/branchs.cpp and in src/ir/notImplemented.cpp */
VOID displayTrace(ADDRINT addr, const std::string &insDis, const std::string &expr, UINT64 isTainted)
{
  std::stringstream addrFormat;
  std::stringstream taintColor;

  /* Sometime, the address must not be display */
  if (addr != 0)
    addrFormat << boost::io::group(hex, showbase, addr);

  /* If taint is enable, the trace is colord */
  if (isTainted)
    taintColor << _GREEN; /* Feel free to choose your color */

  /* Display */
  std::cout << taintColor.str() << boost::format(outputInstruction) % addrFormat.str() % insDis % expr << _ENDC;
}

