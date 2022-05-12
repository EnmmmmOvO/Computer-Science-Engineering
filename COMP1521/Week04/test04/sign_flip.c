#include "sign_flip.h"

// given the 32 bits of a float return it with its sign flipped
uint32_t sign_flip(uint32_t f) {
    int sign = (f >> 31) & 1;
    if (sign == 1) {
        f = f & 0x7fffffff;
    } else {
        f = f | 0x80000000;
    }
    return f;
}
