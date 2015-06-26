#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

uint32_t check(int n)
{
    uint32_t result;
    if (n == 1){
        result = 100;
    }else if(n == 2){
        result = 200;
    }else if (n == 3){
        result = 300;
    }

    return result;
}

int main(int argc, const char **argv)
{
    uint32_t result = check(argc);
    printf("Result = %d\n", result);
    return 0;
}
