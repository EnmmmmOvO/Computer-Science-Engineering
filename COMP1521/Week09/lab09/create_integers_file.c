#include <stdio.h>
#include <stdlib.h>


int main (int argc, char *argv[]) {
    if (argc != 4) {
        fprintf(stderr, "Usage: %s <source file> <destination file>\n", argv[0]);
        return 1;
    }

    FILE *output_stream = fopen(argv[1], "w");

    for (int loop = strtol(argv[2], NULL, 10); loop <= strtol(argv[3], NULL, 10); loop++) {
        fprintf(output_stream, "%d\n", loop);
    }

    fclose(output_stream);
    return 0;
}