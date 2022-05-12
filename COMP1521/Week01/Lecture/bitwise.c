#include <stdio.h>
#include <stdint.h>
#include "print_bits.h"

void print_bits_hex(char *description, uint16_t n);

int main(void) {

    uint16_t a = 0;
    printf("Enter a: ");
    scanf("%hd", &a);

    uint16_t b = 0;
    printf("Enter b: ");
    scanf("%hd", &b);

    printf("Enter c: ");
    int c = 0;
    scanf("%d", &c);

    print_bits_hex("     a = ", a);
    print_bits_hex("     b = ", b);
    print_bits_hex("    ~a = ", ~a);
    print_bits_hex(" a & b = ", a & b);
    print_bits_hex(" a | b = ", a | b);
    print_bits_hex(" a ^ b = ", a ^ b);
    print_bits_hex("a >> c = ", a >> c);
    print_bits_hex("a << c = ", a << c);

    return 0;
}

// print description then print
// binary, hexadecimal and decimal representation of a value
void print_bits_hex(char *description, uint16_t value) {
    printf("%s", description);
    print_bits(value, 8 * sizeof value);
    printf(" = 0x%04x = %d\n", value & 0xFFFF, value);
}