#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

uint32_t hex_to_int(char *ch);

int main (int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <exponent>\n", argv[0]);
        return 1;
    }

    char *character = argv[1];
    uint32_t value = hex_to_int(character);
    printf("%s hexadecimal is %u base 10\n", argv[1], value);
    return 0;
}

uint32_t hex_to_int(char *ch) {
    uint32_t value = 0;
    for (int loop = 0; ch[loop] != 0; loop ++) {
        int ch_to_int = ch[loop];
        int int_value = 0;
        if (ch_to_int >= 'A' && ch_to_int <= 'F') {
            int_value = 10 + ch_to_int - 'A';
        } else if (ch_to_int >= '0' && ch_to_int <= '9') {
            int_value = ch_to_int - '0';
        } else {
            fprintf(stderr, "Bad digit '%c'\n", ch_to_int);
            exit(1);
        }
        value <<= 4;
        value |= int_value;
    }
    return value;
}