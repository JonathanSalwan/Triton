#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>

int myatoi(char *p) {
    int i = 0;

    while (*p != '\x00' && *p >= '0' && *p <= '9') {
        i *= 10;
        i += *(unsigned char *)p - '0';
        p++;
    }

    return i;
}


int main(int argc, char *argv[]) {
    char buffer[10] = { 0 };
    int i;
    if (argc != 2) {
        printf("Usage: %s <string>\n", argv[0]);
        exit(-1);
    }


    i = myatoi(argv[1]);

    if (i == 33) {
        printf("ok\n");
    }

    return 0;
}
