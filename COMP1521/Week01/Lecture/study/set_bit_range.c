#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

int main (int argc, char *argv[]) {
    if (argc != 3) {
        fprintf(stderr, "Usage: %s <exponent>\n", argv[0]);
        return 1;
    }
    
    int start = strtol(argv[1], NULL, 0);
    int end = strtol(argv[2], NULL, 0);

    uint32_t value = 1;
    value <<= end + 1;
    value -= 1;
    uint32_t temp = 1;
    temp <<= start;
    temp -= 1;
    value -= temp;

    printf("Bits %d to %d of %u are ones:\n", start, end, value);
    for (int loop = 31; loop >= 0; loop --) {
        uint64_t uint64_value = value >> loop;
        int bit = uint64_value & 1;
        printf("%d", bit);
    }
    printf("\n");
    return 0;
}