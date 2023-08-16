// Simple wc emulation for a COMP2041/9044 lecture example
// written by andrewt@unsw.edu.au

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>

// count lines, words, chars in stream
// assumes Unix-like line separator '\n'
// breaks on other platforms, see https://en.wikipedia.org/wiki/Newline

void process_stream(FILE *in, char *name) {
    int n_lines = 0;
    int n_words = 0;
    int n_chars = 0;
    int in_word = 0;
    int c;

    while ((c = fgetc(in)) != EOF) {
        n_chars++;

        if (c == '\n') {
            n_lines++;
        }

        if (isspace(c)) {
            in_word = 0;
        } else if (!in_word) {
            in_word = 1;
            n_words++;
        }
    }

    printf("%d %d %d %s\n", n_lines, n_words, n_chars, name);
}

// process files given as arguments
// if no arguments process stdin
int main(int argc, char *argv[]) {
    if (argc == 1) {
        process_stream(stdin, "stdin");
    } else {
        for (int i = 1; i < argc; i++) {
            FILE *in = fopen(argv[i], "r");
            if (in == NULL) {
                fprintf(stderr, "%s: %s: ", argv[0], argv[i]);
                perror("");
                return 1;
            }
            process_stream(in, argv[i]);
            fclose(in);
        }
    }
    return 0;
}
