#include <stdio.h>
#include <ctype.h>

int main(int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <source file>\n", argv[0]);
        return 1;
    }

    FILE *input_stram = fopen(argv[1], "rb");
    int c = fgetc(input_stram);

    for (long loop = 0; c != EOF; loop++, c = fgetc(input_stram)) {   
        printf("byte %4ld: %3d 0x%02x", loop, c, c);
        if (isprint(c)) printf(" '%c'", 'A'+ c - 65);
        printf("\n");
    }
    
    fclose(input_stram);
    return 0;
}