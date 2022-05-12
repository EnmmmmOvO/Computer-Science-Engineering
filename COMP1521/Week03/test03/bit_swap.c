// swap pairs of bits of a 64-bit value, using bitwise operators

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

// return value with pairs of bits swapped
uint64_t bit_swap(uint64_t value) {
    uint64_t a = (value >> 1) & 0x5555555555555555;
    uint64_t b = (value << 1) & 0xaaaaaaaaaaaaaaaa;
    return a | b;
}
