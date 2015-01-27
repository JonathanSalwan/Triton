
#include "pin.H"
#include "Triton.h"

#define _BLUE   "\033[94m"
#define _GREEN  "\033[92m"
#define _YELLOW "\033[93m"
#define _RED    "\033[91m"
#define _ENDC   "\033[0m"

/* Output format */
boost::format outputInstruction("%1% %|15t| %2% %|55t| %3%\n");



VOID displayTrace(ADDRINT addr, const std::string &insDis, const std::string &expr, UINT64 isTainted)
{
  std::stringstream addrFormat;
  std::stringstream taintColor;

  if (addr != 0)
    addrFormat << boost::io::group(hex, showbase, addr);

  if (isTainted)
    taintColor << _GREEN;

  std::cout << taintColor.str() << boost::format(outputInstruction) % addrFormat.str() % insDis % expr << _ENDC;
}

