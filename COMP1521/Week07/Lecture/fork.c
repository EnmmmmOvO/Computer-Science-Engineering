#include <stdio.h>
#include <unistd.h>

int main (void) {
    pid_t pid = fork();
    if (pid == -1) {
        perror("fork");
    } else if (pid == 0) {
        printf("I am the child because fork() returned %d.\n", pid);
    } else {
        printf("I am the child because fork() returned %d.\n", pid);
    }
    return 0;
}