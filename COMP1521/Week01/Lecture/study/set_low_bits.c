#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

int main (int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <exponent>\n", argv[0]);
        return 1;
    }

    int position = strtol(argv[1], NULL, 0);
    uint32_t value = 1;
    value <<= position;
    value -= 1;
    printf("The bottom %d bits of %u arer ones:\n", position, value);
    for (int loop = 31; loop >= 0; loop --) {
        uint64_t uint64_value = value >> loop;
        int bit = uint64_value & 1;
        printf("%d", bit);
    }
    printf("\n");
    return 0;
}