#include <stdio.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <assert.h>

int main(int argc, char *argv[]) {
    struct stat s;
    if (stat(argv[1], &s) == 0 && (s.st_mode & S_IFMT) == S_IFDIR) {
        printf("1\n");
    } else {
        printf("0\n");
    }
    return 0;
}