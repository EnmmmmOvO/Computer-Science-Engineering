#include <stdio.h>
#include <unistd.h>
#include <sys/wait.h>
#include <spawn.h>

int main (void) {
    int pipe_file_descriptors[2];
    if (pipe(pipe_file_descriptors) == EOF) {
        perror("pipe");
        return 1;
    }

    posix_spawn_file_actions_t action;
    if (posix_spawn_file_actions_init(&action) != 0) {
        perror("posix_spawn_file_actions_init");
        return 1;
    }

    if (posix_spawn_file_actions_addclose(&action, pipe_file_descriptors[1]) != 0) {
        perror("posix_spawn_file_actions_addclose");
        return 1;
    }

    if (posix_spawn_file_actions_adddup2(&action, pipe_file_descriptors[0], 0) != 0) {
        perror("posix_spawn_file_actions_addup2");
        return 1;
    }
    

    pid_t pid;
    extern char **environ;
    char *sort_argv[] = {"sort", NULL};
    if (posix_spawn(&pid, "/usr/bin/sort", &action, NULL, sort_argv, environ) != 0) {
        perror("posix_spawn");
        return 1;
    }

    close(pipe_file_descriptors[0]);

    FILE *p = fdopen(pipe_file_descriptors[1], "w");
    if (p == NULL) {
        perror("fdopen");
        return 1;
    }

    fprintf(p, "sort\nwords\nplease\nthese\n");

    fclose(p);

    int exit_status;
    if (waitpid(pid, &exit_status, 0) == -1) {
        perror("waitpid");
        return 1;
    }
    printf("/usr/bin/sort exit status was %d\n", exit_status);

    posix_spawn_file_actions_destroy(&action);
    return 0;
}
