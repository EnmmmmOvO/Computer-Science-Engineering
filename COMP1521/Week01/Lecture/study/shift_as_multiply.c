#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

int main (int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <exponent>\n", argv[0]);
        return 1;
    }
    uint32_t value = 1;
    int position = strtol(argv[1], NULL, 0);
    value <<= position;
    printf("2 to the power of %d is %u\n", position, value);
    printf("In binary it is : ");
    for (int loop = 31; loop >= 0; loop --) {
        uint64_t uint64_value = value >> loop;
        int bit = uint64_value &1;
        printf("%d", bit);
    }
    printf("\n");
    return 0;
}