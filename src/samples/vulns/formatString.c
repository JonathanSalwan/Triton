#include <stdio.h>
#include <stdlib.h>

void check(char *buf)
{
  unsigned int i;
  char *ptr;

  if (!(ptr = malloc(12)))
    return;

  for (i = 0; i < 8; i++)
    ptr[i] = buf[i]; /* spread the taint to another area */
  ptr[i] = '\0';

  printf(ptr);       /* warn format string */
}

int main(int ac, char **av)
{
  if (ac < 2)
    return 0;
  check(av[1]); 
}
