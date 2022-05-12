#include <stdio.h>
#include <unistd.h>

int main (void) {
    extern char **environ;
    for (int loop = 0; environ[loop] != NULL; loop++) {
        printf("%s\n", environ[loop]);
    }

    return 0;
}