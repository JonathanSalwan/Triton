
#include <stdio.h>
#include <stdlib.h>

char *serial = "\x31\x3e\x3d\x26\x31";

int check(char *ptr)
{
  int i;
  int hash = 0xABCD;

  for (i = 0; ptr[i]; i++)
    hash += ptr[i] ^ serial[i % 5];

  return hash;
}

int main(int ac, char **av)
{
  int ret;

  if (ac != 2)
    return -1;

  ret = check(av[1]);
  if (ret == 0xad6d)
    printf("Win\n");
  else
    printf("fail\n");

  return 0;
}

