#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

char *int_to_hex_string(uint32_t n);

int main(void) {
    uint32_t a = 0;
    printf("Enter a positive int: ");
    scanf("%u", &a);

    char *hex_string = int_to_hex_string(a);

    // print the returned string
    printf("%u = 0x%s\n", a, hex_string);

    free(hex_string);

    return 0;
}

// return a malloced string containing the hexadecimal digits of n

char *int_to_hex_string(uint32_t n) {
    // sizeof returns number of bytes in n's representation
    // each byte is 2 hexadecimal digits

    int n_hex_digits = 2 * (sizeof n);

    // allocate memory to hold the hex digits + a terminating 0
    char *string = malloc(n_hex_digits + 1);

    // print hex digits from most significant to least significant

    for (int which_digit = 0; which_digit < n_hex_digits; which_digit++) {
        // shift value across so hex digit we want
        // is in bottom 4 bits

        int bit_shift = 4 * which_digit;
        uint32_t shifted_value = n >> bit_shift;

        // mask off (zero) all bits but the bottom 4 bites

        int hex_digit = shifted_value & 0xF;

        // hex digit will be a value 0..15
        // obtain the corresponding ASCII value
        // "0123456789ABCDEF" is a char array
        // containing the appropriate ASCII values

        int hex_digit_ascii = "0123456789ABCDEF"[hex_digit];

        string[which_digit] = hex_digit_ascii;
    }

    // 0 terminate the array
    string[n_hex_digits] = 0;

    return string;
}