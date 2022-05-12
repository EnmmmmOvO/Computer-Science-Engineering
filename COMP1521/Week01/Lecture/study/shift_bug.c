#include <stdio.h>
#include <stdint.h>


int main (int argc, char *argv[]) {
    int16_t i;
    i = -1;
    i >>= 1;
    printf("%d\n", i);
    i = -1;
    i <<= 1;
    printf("%d\n", i);
    i = 32767;
    i <<= 1;
    uint64_t j ;
    j = 1 << 33;
    j = ((uint64_t)1) << 33;
    return 0;
}