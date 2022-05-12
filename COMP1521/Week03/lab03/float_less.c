// Compare 2 floats using bit operations only

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

uint32_t extract_bit_range(uint32_t value, int high, int low);
int is_nan(float_components_t fc);
int negitive_positive(float_components_t fc1, float_components_t fc2);
float uint32_float(uint32_t bits);

// float_less is given the bits of 2 floats bits1, bits2 as a uint32_t
// and returns 1 if bits1 < bits2, 0 otherwise
// 0 is return if bits1 or bits2 is Nan
// only bit operations and integer comparisons are used
uint32_t float_less(uint32_t bits1, uint32_t bits2) {
    float_components_t bits_1 = float_bits(bits1);
    float_components_t bits_2 = float_bits(bits2);

    if (is_nan(bits_1) == 0 || is_nan(bits_2) == 0) 
        return 0;

    if (bits1 == 0 && bits2 == 0)
        return 0;

    switch(negitive_positive(bits_1, bits_2)) {
        case 1: return 1;
        case 2: return 0; 
    }

    float float1 = uint32_float(bits1);
    float float2 = uint32_float(bits2);

    if (float1 < float2) {
        return 1;
    }


    return 0;
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

int is_nan(float_components_t fc) {
    if (fc.exponent == 255 && fc.fraction != 0) {
        return 0;
    }
    return 1;
}

int negitive_positive(float_components_t fc1, float_components_t fc2) {
    if (fc1.sign > fc2.sign) {
        return 1;
    } else if (fc1.sign < fc2.sign) {
        return 2;
    }
    return 0;
}

float uint32_float(uint32_t bits) {
    union overlay input;
    input.u = bits;
    return input.f; 
}
