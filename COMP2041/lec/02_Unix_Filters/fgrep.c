// Simple fgrep emulation for a COMP2041/9044 lecture example
// andrewt@unsw.edu.au


#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// print lines containing the specified substring
void process_stream(FILE *stream, char *name, char *substring) {
    char *line = NULL;
    size_t line_size = 0;
    int line_number = 1;

    while (getline(&line, &line_size, stream) > 0) {
        if (strstr(line, substring) != NULL) {
            printf("%s:%d:%s", name, line_number, line);
        }
        line_number++;
    }

    free(line);
}

// process files given as arguments
// if no arguments process stdin
int main(int argc, char *argv[]) {

    if (argc == 2) {
        process_stream(stdin, "<stdin>", argv[1]);
    } else {
        for (int i = 2; i < argc; i++) {
            FILE *in = fopen(argv[i], "r");
            if (in == NULL) {
                fprintf(stderr, "%s: %s: ", argv[0], argv[i]);
                perror("");
                return 1;
            }
            process_stream(in, argv[i], argv[1]);
            fclose(in);
        }
    }

    return 0;
}
