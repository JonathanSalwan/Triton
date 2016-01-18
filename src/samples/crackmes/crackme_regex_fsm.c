/*
 * From: http://doar-e.github.io/blog/2013/08/24/regular-expressions-obfuscation-under-the-microscope
 */

#include <stdio.h>
#include <string.h>

unsigned char check(char* s) {
  unsigned int state = 0, i = 0;

  do {
    switch(state) {
      case 0:
        if(*s == 'H')
          state = 1;
        break;

      case 1:
        if(*s == 'i')
          state = 2;
        else
          return 0;
        break;

      case 2:
        if(*s == '-')
          state = 3;
        else
          return 0;
        break;

      case 3:
      case 4:
      case 5:
      case 6:
        if(*s >= '0' && *s <= '9')
          state++;
        else
          return 0;
        break;

      case 7:
        return 1;
    }
  } while(*s++);

  return 0;
}


int main(int argc, char *argv[])
{
  if(argc != 2) {
      printf("./fsm <string>\n");
      return 0;
  }

  if(check(argv[1]))
    printf("Good boy.\n");
  else
    printf("Bad boy.\n");

  return 1;
}
