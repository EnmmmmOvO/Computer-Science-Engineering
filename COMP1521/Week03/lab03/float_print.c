// Print out a float.

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

uint32_t extract_bit_range(uint32_t value, int high, int low);

//
// float_print is given the bits of a float as a uint32_t
// it prints out the float in the same format as "%.9g\n"
// using only putchar & puts
//
void float_print(uint32_t bits) {
    
}
