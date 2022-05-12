#include <stdio.h>
#include <stdlib.h>


int main (int argc, char *argv[]) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <source file> <destination file>\n", argv[0]);
        return 1;
    }

    FILE *output_stream = fopen(argv[1], "w");
    for (int loop = 2; loop < argc; loop++) {
        fputc(strtol(argv[loop], NULL, 10), output_stream);
    }
    
    fclose(output_stream);
    return 0;
}