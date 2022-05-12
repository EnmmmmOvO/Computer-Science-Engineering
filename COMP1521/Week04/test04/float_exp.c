#include "float_exp.h"

#define EXPONENT_HIGH_BIT  30
#define EXPONENT_LOW_BIT   23

uint32_t extract_bit_range(uint32_t value, int high, int low) {
    uint32_t masks = (((uint32_t)1) << (high - low + 1)) - 1;
    return (value >> low) & masks;
}

// given the 32 bits of a float return the exponent
uint32_t float_exp(uint32_t f) {
    return extract_bit_range(f, EXPONENT_HIGH_BIT, EXPONENT_LOW_BIT);
}
