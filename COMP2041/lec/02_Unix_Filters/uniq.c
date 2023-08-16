// Simple uniq emulation for a COMP2041/9044 lecture example
// andrewt@unsw.edu.au

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

// cope stream to stdout except for repeated lines
void process_stream(FILE *stream) {
    char *line = NULL;
    size_t line_size = 0;
    char *last_line = NULL;
    size_t last_line_size = 0;

    while (getline(&line, &line_size, stream) > 0) {
        if (last_line == NULL || strcmp(line, last_line) != 0) {
            fputs(line, stdout);
        }

        // grow last_line if line has grown
        if (last_line_size != line_size) {
            last_line = realloc(last_line, line_size);
            assert(last_line != NULL);
            last_line_size = line_size;
        }

        strncpy(last_line, line, line_size);
    }

    free(line);
    free(last_line);
}

// process files given as arguments
// if no arguments process stdin
int main(int argc, char *argv[]) {
    if (argc == 1) {
        process_stream(stdin);
    } else {
        FILE *in = fopen(argv[1], "r");
        if (in == NULL) {
            fprintf(stderr, "%s: %s: ", argv[0], argv[1]);
            perror("");
            return 1;
        }
        process_stream(in);
        fclose(in);
    }

    return 0;
}
