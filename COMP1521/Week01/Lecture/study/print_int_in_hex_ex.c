#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

int main (int argc, char *argv[]) {
    uint32_t value = 0;
    printf("Enter a positive int : ");
    scanf("%u", &value);
    printf("%u = 0x", value);  

    int size = 2 * (sizeof value);
    for (int loop = size - 1; loop >= 0; loop --) {
        int shift = 4 * loop;
        uint32_t value_sh = value >> shift;
        int value_shift = value_sh & 0xF;
        int hex_digit_ascii = "0123456789ABCDEF"[value_shift];
        putchar(hex_digit_ascii);

    }  
    printf("\n");
    return 0;
}