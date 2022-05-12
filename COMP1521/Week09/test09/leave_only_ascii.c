#include <stdio.h>

int main(int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <source file>\n", argv[0]);
        return 1;
    }

    FILE *input_stream = fopen(argv[1], "r");
    FILE *output_stream = fopen("temp.txt", "w");
    int c = fgetc(input_stream);

    int number = 0;
    for (int loop = 0; c != EOF; loop++, c = fgetc(input_stream)) {
        if (c >= 0 && c < 128) {
            fprintf(output_stream, "%c", c);
        } else {
            number ++;
        }
    }

    fclose(input_stream);
    fclose(output_stream);
    
    if (number != 0) {
        remove(argv[1]);
        rename("temp.txt", argv[1]);
    }
    
    return 0;
}