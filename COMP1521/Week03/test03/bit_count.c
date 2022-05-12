// count bits in a uint64_t

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

#define N_BITS 64
// return how many 1 bits value contains
int bit_count(uint64_t value) {
    int bits = 0;
    for (int loop = N_BITS - 1; loop >= 0; loop --) {
        int bit = (value >> loop) & 1;
        if (bit == 1) {
            bits ++;
        }
    }
    return bits;
}
