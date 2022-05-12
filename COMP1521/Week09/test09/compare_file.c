#include <stdio.h>

int main(int argc, char *argv[]) {
    if (argc != 3) {
        fprintf(stderr, "Usage: %s <source file>\n", argv[0]);
        return 1;
    }

    FILE *input_stream1 = fopen(argv[1], "r");
    FILE *input_stream2 = fopen(argv[2], "r");

    int c = fgetc(input_stream1);
    int d = fgetc(input_stream2);

    for (int loop = 0; c != EOF && d != EOF; loop++, d = fgetc(input_stream2), c = fgetc(input_stream1)) {        
        if (c != d) {
            printf("Files differ at byte %d\n", loop);
            fclose(input_stream1);
            fclose(input_stream2);
            return 0;
        }
    }

    if (c == EOF && d == EOF) {
        printf("Files are identical\n");
    } else if (c == EOF && d != EOF) {
        printf("EOF on %s\n", argv[1]);
    } else if (c != EOF && d == EOF) {
        printf("EOF on %s\n", argv[2]);
    }

    fclose(input_stream1);
    fclose(input_stream2);
    return 0;
}