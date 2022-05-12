#include <stdio.h>
#include <float.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <string.h>

union overlay_float {
    float f;
    uint32_t u;
};

void display_float(char *ch);
uint32_t convert_bitstring_to_uint32(char *ch);
uint32_t convert_float_to_uint32(float number);
void print_32bit(uint32_t number);
void print_float_details(uint32_t value);
uint32_t extract_bit_range(uint32_t value, int start, int end);

int main (int argc, char *argv[]) {
    for (int loop = 1; loop < argc; loop ++) 
        display_float(argv[loop]);
    return 0;        
}

#define N_BITS             32
#define SIGN_BIT           31
#define EXPONENT_HIGH_BIT  30
#define EXPONENT_LOW_BIT   23
#define FRACTION_HIGH_BIT  22
#define FRACTION_LOW_BIT    0

#define EXPONENT_OFFSET   127
#define EXPONENT_INF_NAN  255


void display_float(char *ch) {
    uint32_t value;
    if (strlen(ch) == N_BITS && strspn(ch, "01") == N_BITS) {
        value = convert_bitstring_to_uint32(ch);
    } else {
        float number = strtof(ch, NULL);
        value = convert_float_to_uint32(number);
        printf("%s is represented as IEEE-754 single-precision by these bits:\n", ch);
        print_32bit(value);
    }
    print_float_details(value);
}


uint32_t convert_bitstring_to_uint32(char *ch) {
    uint32_t value = 0;
    uint32_t masks = 1;
    for (int loop = N_BITS - 1; loop >= 0; loop --) {
        if (ch[loop] == '1') 
            value |= masks;
        if (loop != 0)
            masks <<= 1;
    }
    return value;
}

uint32_t convert_float_to_uint32(float number) {
    union overlay_float overlay;
    overlay.f = number;
    return overlay.u;
}

void print_32bit(uint32_t number) {
    for (int loop = N_BITS - 1; loop >= 0; loop --) {
        int bit = (number >> loop) & 1;
        printf("%d", bit);
    }
    printf("\nsign | exponent | fraction\n   ");
    for (int loop = N_BITS - 1; loop >= 0; loop --) {
        int bit = (number >> loop) & 1;
        printf("%d", bit);
        if (loop == SIGN_BIT || loop == EXPONENT_LOW_BIT)
            printf(" | ");
    }
    printf("\n");
}

void print_float_details(uint32_t value) {
    int sign = (value >> SIGN_BIT) & 1;
    printf("sign bit = %d\n", sign);
    if (sign == 1) {
        printf("sign = -\n");
        sign = -1;
    } else {
        printf("sign = +\n");
        sign = 1;
    }

    uint32_t exponent = extract_bit_range(value, EXPONENT_LOW_BIT, EXPONENT_HIGH_BIT);
    uint32_t fraction = extract_bit_range(value, FRACTION_LOW_BIT, FRACTION_HIGH_BIT);
    
    printf("raw exponent    = ");
    for (int loop = EXPONENT_HIGH_BIT; loop >= EXPONENT_LOW_BIT; loop --) {
        int bit = (value >> loop) & 1;
        printf("%d", bit);
    } 
    printf(" binary\n                = %u decimal\n", exponent);

    if (exponent == EXPONENT_INF_NAN) {
        if (fraction == 0) {
            if (sign == 1)
                printf("number = +inf\n");
            else 
                printf("number = -inf\n");
        } else {
            printf("number = NaN\n");
        }
        return;
    }

    printf("actual exponent = %u - exponent_bias\n", exponent);
    printf("                = %u - 127\n", exponent);
    int actual_exponent = exponent - EXPONENT_OFFSET;
    printf("                = %d\n", actual_exponent);


    printf("number = %d.", sign);
    for (int loop = FRACTION_HIGH_BIT; loop >= FRACTION_LOW_BIT; loop --) {
        int bit = (value >> loop) & 1;
        printf("%d", bit);
    }
    printf(" binary * 2**%d\n", actual_exponent);

    double number = sign * (1 + fraction / pow(2, EXPONENT_LOW_BIT));
    printf("       = %g decimal * 2**%d\n", number, actual_exponent);
    printf("       = %g decimal * %g\n", number, pow(2, actual_exponent));
    printf("       = %g\n", number * pow(2, actual_exponent));
}

uint32_t extract_bit_range(uint32_t value, int start, int end) {
    uint32_t mask = (((uint32_t)1) << (end - start + 1)) - 1;
    return (value >> start) & mask;
}