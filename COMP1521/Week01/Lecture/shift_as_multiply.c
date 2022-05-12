#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include "print_bits.h"

int main(int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <exponent>\n", argv[0]);
        return 1;
    }

    int n = strtol(argv[1], NULL, 0);

    uint32_t power_of_two;


    int n_bits = 8 * sizeof power_of_two;
    print_bits("%d\n", n_bits);

    if (n >= n_bits) {
        fprintf(stderr, "n is too large\n");
        return 1;
    }

    power_of_two = 1;
    power_of_two = power_of_two << n;

    printf("2 to the power of %d is %u\n", n, power_of_two);

    printf("In binary it is: ");
    print_bits(power_of_two, n_bits);
    printf("\n");

    return 0;
}