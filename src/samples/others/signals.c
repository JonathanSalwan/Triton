
#include <signal.h>


int main(int ac, const char **av)
{
  raise (SIGSEGV);
  return 0;
}

