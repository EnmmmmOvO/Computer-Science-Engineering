// Simple sort emulation for a COMP2041/9044 lecture example
// andrewt@unsw.edu.au

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int cmpstringp(const void *p1, const void *p2)
{
   return strcmp(* (char * const *) p1, * (char * const *) p2);
}


// print lines of stream in sorted order
void process_stream(FILE *stream) {
    char *line = NULL;
    size_t line_size = 0;
    char **lines = NULL;
    size_t lines_size = 0;

    while (getline(&line, &line_size, stream) > 0) {
        lines = realloc(lines, ++lines_size*sizeof(lines[0]));
        lines[lines_size-1] = line;
        line = NULL;
        line_size = 0;
    }
    free(line);

    qsort(lines, lines_size, sizeof(lines[0]), cmpstringp);

    for (size_t i = 0; i < lines_size; i++) {
        fputs(lines[i], stdout);
        free(lines[i]);
    }
    free(lines);
}

// process files given as arguments
// if no arguments process stdin
int main(int argc, char *argv[]) {

    if (argc == 1) {
        process_stream(stdin);
    } else {
        for (int i = 1; i < argc; i++) {
            FILE *in = fopen(argv[i], "r");
            if (in == NULL) {
                fprintf(stderr, "%s: %s: ", argv[0], argv[i]);
                perror("");
                return 1;
            }
            process_stream(in);
            fclose(in);
        }
    }

    return 0;
}
