#include <stdio.h>

int main (int argc, char *argv[]) {
    int c;
    while ((c = fgetc(stdin)) != EOF) fputc(c, stdout);
    return 0;
}