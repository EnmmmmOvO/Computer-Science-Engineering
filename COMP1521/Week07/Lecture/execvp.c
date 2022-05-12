#include <stdio.h>
#include <unistd.h>

int main (void) {
    char *echo_argv[] = {"/bin/echo", "good-bye", "cruel", "word", NULL};
    execvp("/bin/echo", echo_argv);

    perror("execv");
}