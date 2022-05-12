#include <stdio.h>
#include <stdint.h>

void print_hex(uint32_t n);

int main(void) {

    uint32_t a = 0;
    printf("Enter a positive int: ");
    scanf("%u", &a);

    printf("%u = 0x", a);
    print_hex(a);
    printf("\n");

    return 0;
}

// print n in hexadecimal

void print_hex(uint32_t n) {

    // sizeof returns number of bytes in n's representation
    // each byte is 2 hexadecimal digits

    int n_hex_digits = 2 * (sizeof n);

    // print hex digits from most significant to least significant

    for (int which_digit = n_hex_digits - 1; which_digit >= 0; which_digit--) {

        // shift value across so hex digit we want
        // is in bottom 4 bits

        int bit_shift = 4 * which_digit;
        uint32_t shifted_value = n >> bit_shift;

        // mask off (zero) all bits but the bottom 4 bites

        int hex_digit = shifted_value & 0xF;

        // hex digit will be a value 0..15
        // obtain the corresponding ASCII value
        // "0123456789ABCDEF" is a char array
        // containing the appropriate ASCII values (+ a '\0')

        int hex_digit_ascii = "0123456789ABCDEF"[hex_digit];

        putchar(hex_digit_ascii);
    }
}