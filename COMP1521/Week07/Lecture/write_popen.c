#include <stdio.h>
#include <stdlib.h>

int main (void) {
    FILE *p = popen("tr a-z A-Z", "w");
    if (p == NULL) {
        perror("");
        exit(1);
    }
    fprintf(p, "plz date me\n");
    fclose(p);
    return 0;
}