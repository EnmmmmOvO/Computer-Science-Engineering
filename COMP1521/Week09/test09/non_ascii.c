#include <stdio.h>

int main(int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <source file>\n", argv[0]);
        return 1;
    }

    FILE *input_stream = fopen(argv[1], "rb");
    int c = fgetc(input_stream);

    int number = 0;
    for (int loop = 0; c != EOF; loop++, c = fgetc(input_stream)) {
        if (c < 0 || c >= 128) {
            number++;
            printf("%s: byte %d is non-ASCII\n", argv[1], loop);
            break;
        }
    }
    if (!number) printf("%s is all ASCII\n", argv[1]);
    fclose(input_stream);
    return 0;
}