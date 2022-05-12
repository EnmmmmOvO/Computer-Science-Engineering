#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <spawn.h>

int main (void) {
    pid_t pid = fork();
    if (pid == -1) {
        perror("fork");
        exit(1);
    } else if (pid == 0) {
        char *data_argv[] = {"/bin/date", "--utc", NULL};
        execvp("/bin/date", data_argv);
        perror("execvp");
    } else {
        int exit_status;
        if (waitpid(pid, &exit_status, 0) == -1) {
            perror("waitpid");
            exit(1);
        }
        printf("/bin/date exit status was %d\n", exit_status);
    }
    
    return 0;
}