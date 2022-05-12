#include <stdio.h>
#include <stdlib.h>
#include <spawn.h>
#include <sys/wait.h>

int main (void) {
    setenv("STATUS", "great", 1);

    char *getenv_argv[] = {"./getenv", NULL};
    extern char **environ;
    pid_t pid;
    if (posix_spawn(&pid, "./getenv", NULL, NULL, getenv_argv, environ) != 0) {
        perror("posix_spawn");
        exit(1);
    }
    int exit_status;
    if (waitpid(pid, &exit_status, 0) == 0) {
        perror("waitpid");
        exit(0);
    }
    return 0;
} 