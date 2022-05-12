#include <stdio.h>

int main (void) {
    char line[BUFSIZ];
    while (fgets(line, sizeof line, stdin) != NULL) {
        fputs(line, stdout);
    } 
    return 0;
}