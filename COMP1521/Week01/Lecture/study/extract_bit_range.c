#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

int main (int argc, char *argv[]) {
    if (argc != 4) {
        fprintf(stderr, "Usage: %s <exponent>\n", argv[0]);
        return 1;
    }

    uint32_t value = strtol(argv[3], NULL , 0);
    int start = strtol(argv[1], NULL, 0);
    int end = strtol(argv[2], NULL, 0);

    printf("Value %u in binary is:\n", value);
    for (int loopA = 31; loopA >= 0; loopA --) {
        uint64_t uint64_value = value >> loopA;
        int bit = uint64_value &1;
        printf("%d", bit);
    }
    printf("\n");

    printf("Bits %d to %d of %u are:\n", start, end, value);
    for (int loopB = end; loopB >= start; loopB --) {
        uint64_t uint64_value = value >> loopB;
        int bit = uint64_value &1;
        printf("%d", bit);
    }
    printf("\n");
    
    return 0;
}