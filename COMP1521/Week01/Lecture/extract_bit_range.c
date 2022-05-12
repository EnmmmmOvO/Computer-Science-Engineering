#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <assert.h>
#include "print_bits.h"

int main(int argc, char *argv[]) {
    if (argc != 4) {
        fprintf(stderr, "Usage: %s <low-bit> <high-bit> <value>\n", argv[0]);
        return 1;
    }

    int low_bit = strtol(argv[1], NULL, 0);
    int high_bit = strtol(argv[2], NULL, 0);
    uint32_t value = strtol(argv[3], NULL, 0);

    uint32_t mask;

    int n_bits = 8 * sizeof mask;

    assert(low_bit >= 0);
    assert(high_bit >= low_bit);
    assert(high_bit < n_bits);

    int mask_size = high_bit - low_bit + 1;

    mask = 1;
    mask = mask << mask_size;
    mask = mask - 1;
    mask = mask << low_bit;

    // get a value with the bits outside the range low_bit..high_bit set to zero
    uint32_t extracted_bits = value & mask;

    // right shift the extracted_bits so low_bit becomes bit 0
    extracted_bits = extracted_bits >> low_bit;

    printf("Value %u in binary is:\n", value);
    print_bits(value, n_bits);
    printf("\n");

    printf("Bits %d to %d of %u are:\n", low_bit, high_bit, value);
    print_bits(extracted_bits, mask_size);
    printf("\n");

    return 0;
}