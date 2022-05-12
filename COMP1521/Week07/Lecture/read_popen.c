#include <stdlib.h>
#include <stdio.h>


int main (void) {
    FILE *p = popen("/bin/date --utc", "r");
    if (p == NULL) {
        perror("");
        return 1;
    }
    char line[256];
    if (fgets(line, sizeof line, p) == NULL) {
        fprintf(stderr, "no output from date\n");
        return 1;
    }
    printf("output captured from /bin/date was: '%s'", line);
    pclose(p);
    return 0;
}