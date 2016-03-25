
#include <stdio.h>
#include <string.h>

int main(int ac, const char *av[]) {
  if (ac < 2)
    return 0;
  printf("%lu\n", strlen(av[1]));
  return 0;
}


