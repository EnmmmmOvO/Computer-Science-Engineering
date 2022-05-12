#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <xor-value>\n", argv[0]);
        return 1;
    }

    int xor_value = strtol(argv[1], NULL, 0);

    if (xor_value < 0 || xor_value > 255) {
        fprintf(stderr, "Usage: %s <xor-value>\n", argv[0]);
        return 1;
    }

    int c;
    while ((c = getchar()) != EOF) {
        //    exclusive-or
        //    ^  | 0  1
        //   ----|-----
        //    0  | 0  1
        //    1  | 1  0

        int xor_c = c ^ xor_value;

        putchar(xor_c);
    }

    return 0;
}