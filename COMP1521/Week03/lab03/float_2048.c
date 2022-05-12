// Multiply a float by 2048 using bit operations only

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <assert.h>

#include "floats.h"

#define N_BITS             32
#define SIGN_BIT           31
#define EXPONENT_HIGH_BIT  30
#define EXPONENT_LOW_BIT   23
#define FRACTION_HIGH_BIT  22
#define FRACTION_LOW_BIT    0
#define EXPONENT_INF_NAN   255

uint32_t extract_bit_range(uint32_t value, int high, int low);

// float_2048 is given the bits of a float f as a uint32_t
// it uses bit operations and + to calculate f * 2048
// and returns the bits of this value as a uint32_t
//
// if the result is too large to be represented as a float +inf or -inf is returned
//
// if f is +0, -0, +inf or -inf, or Nan it is returned unchanged
//
// float_2048 assumes f is not a denormal number
//
uint32_t float_2048(uint32_t f) {
    float_components_t fc  = float_bits(f);
    uint64_t temp = fc.sign;

    if (fc.exponent == EXPONENT_INF_NAN || fc.exponent == 0) {
        return f;
    }

    uint32_t number = 22;
    number <<= FRACTION_HIGH_BIT;
    f += number;
    
    fc  = float_bits(f);
    if (fc.exponent > EXPONENT_INF_NAN || temp != fc.sign) {
        fc.exponent = EXPONENT_INF_NAN;
        fc.fraction = 0;
        return (temp << SIGN_BIT) | (fc.exponent << EXPONENT_LOW_BIT) | fc.fraction;
    }

    return f;
}

float_components_t float_bits(uint32_t f) {
    struct float_components fc;
    fc.sign = f >> SIGN_BIT;
    fc.exponent = extract_bit_range(f, EXPONENT_HIGH_BIT, EXPONENT_LOW_BIT);
    fc.fraction = extract_bit_range(f, FRACTION_HIGH_BIT, FRACTION_LOW_BIT);
    return fc;
}

uint32_t extract_bit_range(uint32_t value, int high, int low) {
    uint32_t masks = (((uint32_t)1) << (high - low + 1)) - 1;
    return (value >> low) & masks;
}