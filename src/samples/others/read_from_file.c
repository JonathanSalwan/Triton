#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <sys/types.h>

#define FILE_PATH "/etc/passwd"


int main(int ac, const char* av[]) {
  char data[32] = {0};
  int fd = -1;

  fd = open(FILE_PATH, O_RDONLY);
  if (fd < 0)
    return -1;

  read(fd, data, sizeof(data));
  if (*(unsigned int*)data == 0x464c457f)
    printf("[+] ELF binary\n");
  else
    printf("[+] Not an ELF binary\n");

  close(fd);
  return 0;
}

