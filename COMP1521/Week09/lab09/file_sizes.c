#include <stdio.h>
#include <sys/stat.h>

int main (int argc, char *argv[]) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <source file> <destination file>\n", argv[0]);
        return 1;
    }
    
    long total = 0;
    for (int loop = 1; loop < argc; loop++) {
        struct stat s;
        if (stat(argv[loop], &s) != 0) {
            perror(argv[loop]);
            continue;
        }
        total += (long)s.st_size;
        printf("%s: %ld bytes\n", argv[loop], (long)s.st_size);
    }

    printf("Total: %ld bytes\n", total);
    return 0;
}