#include <stdio.h>
#include <spawn.h>
#include <stdlib.h>
#include <sys/wait.h>


int main (int argc, char *argv[]) {
    pid_t pid;
    extern char **environ;
    char *ls_argv[] = {"/bin/ls", "-ld", NULL};
    if (posix_spawn(&pid, "/bin/ls" ,NULL, NULL, ls_argv, environ) != 0) {
        perror("pid");
        exit(1);
    }

    if (waitpid(pid, NULL, 0) == -1) {
        perror("waitpid");
        exit(1);
    }
    return 0;
}