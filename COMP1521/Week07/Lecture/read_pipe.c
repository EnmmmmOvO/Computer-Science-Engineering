#include <stdio.h>
#include <stdlib.h>
#include <spawn.h>
#include <sys/wait.h>
#include <unistd.h>

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

    if (posix_spawn_file_actions_addclose(&action, pipe_file_descriptors[0]) != 0) {
        perror("posix_spawn_file_actions_addclose");
        return 1;
    }

    if (posix_spawn_file_actions_adddup2(&action, pipe_file_descriptors[1], 1) != 0) {
        perror("posix_spawn_file_actions_adddup2");
        return 1;
    }

    pid_t pid;
    extern char **environ;
    char *date_argv[] = {"/bin/date", "--utc", NULL};
    if (posix_spawn(&pid, "/bin/date", &action, NULL, date_argv, environ) != 0) {
        perror("posix_spawn");
        return 1;
    }
    
    close(pipe_file_descriptors[1]);
    
    FILE *p = fdopen(pipe_file_descriptors[0], "r");
    if (p == NULL) {
        perror("fdopen");
        exit(1);
    }
    
    char line[256];
    if (fgets(line, sizeof line, p) == NULL) {
        fprintf(stderr, "no output from date\n");
        return 1;
    }
    printf("output captured from /bin/date was: %s", line);

    fclose(p);
    
    int exit_status;
    if (waitpid(pid, &exit_status, 0) == -1) {
        perror("waitpid");
        return 1;
    }

    printf("/bin/date exit status was %d\n", exit_status);
    posix_spawn_file_actions_destroy(&action);;
    return 0;
}
