// Simple /bin/echo emulation for a COMP2041/9044 lecture example
// andrewt@cse.unsw.edu.au

#include <stdio.h>

// print arguments to stdout
int main(int argc, char *argv[]) {

    for (int i = 1; i < argc; i++) {
        if (i > 1) {
            fputc(' ', stdout);
        }
        fputs(argv[i], stdout);
    }
    fputc('\n', stdout);

    return 0;
}
