
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>

char *serial = "\x31\x3e\x3d\x26\x31";

int check(char *ptr)
{
  int i = 0;

  while (i < 5){
    if (((ptr[i] - 1) ^ 0x55) != serial[i])
      return 1;
    i++;
  }
  return 0;
}

int main(int ac, char **av)
{
  int ret, fd;
  char buf[260] = {0};
  char *r = buf;

  fd = open("serial.txt", O_RDONLY);
  read(fd, r, 256);
  close(fd);

  ret = check(r);
  if (ret == 0)
    printf("Win\n");
  else
    printf("loose\n");

  return ret;
}

