#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

uint32_t hex_string_to_int(char *hex_string);
int hex_digit_to_int(int ascii_digit);

int main(int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <hexadecimal-number>\n", argv[0]);
        return 1;
    }

    char *hex_string = argv[1];

    uint32_t u = hex_string_to_int(hex_string);

    printf("%s hexadecimal is %u base 10\n", hex_string, u);

    return 0;
}

uint32_t hex_string_to_int(char *hex_string) {
    uint32_t value = 0;

    for (int which_digit = 0; hex_string[which_digit] != 0; which_digit++) {
        int ascii_hex_digit = hex_string[which_digit];
        int digit_as_int = hex_digit_to_int(ascii_hex_digit);

        value = value << 4;
        value = value | digit_as_int;
    }

    return value;
}

// given the ascii value of a hexadecimal digit
// return the corresponding integer

int hex_digit_to_int(int ascii_digit) {
    if (ascii_digit >= '0' && ascii_digit <= '9') {
        // the ASCII characters '0' .. '9' are contiguous
        // in other words they have consecutive values
        // so subtract the ASCII value for '0' yields the corresponding integer

        return ascii_digit - '0';
    }

    if (ascii_digit >= 'A' && ascii_digit <= 'F') {
        // for characters 'A' .. 'F' obtain the
        // corresponding integer for a hexadecimal digit

        return 10 + (ascii_digit - 'A');
    }

    fprintf(stderr, "Bad digit '%c'\n", ascii_digit);
    exit(1);
}