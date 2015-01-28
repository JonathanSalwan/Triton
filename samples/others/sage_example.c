
#include <signal.h>

void check(const char *buf)
{
  int n = 0;
  if (buf[0] == 'b') n++;
  if (buf[1] == 'a') n++;
  if (buf[2] == 'd') n++;
  if (buf[3] == '!') n++;
  if (n == 4){
    raise(SIGSEGV);
  }
}

int main(int ac, const char **av)
{
  check(av[1]);
  return 0;
}

