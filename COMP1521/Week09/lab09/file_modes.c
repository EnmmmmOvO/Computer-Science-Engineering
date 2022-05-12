#include <stdio.h>
#include <sys/stat.h>

void print(unsigned i);

int main (int argc, char *argv[]) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <source file> <destination file>\n", argv[0]);
        return 1;
    }

    for (int loop = 1; loop < argc; loop++) {
        struct stat s;
        if (stat(argv[loop], &s) != 0) {
            perror(argv[loop]);
            continue;
        }

        switch (s.st_nlink) {
            case 1: printf("-"); break;
            case 2: printf("d"); break;
            default: break;
        }

        print(s.st_mode >> 6 & 7);
        print(s.st_mode >> 3 & 7);
        print(s.st_mode & 7);
        
        printf(" %s\n", argv[loop]);
    }
    return 0; 
}

void print(unsigned i) {
    switch (i) {
        case 0: printf("---"); break;
        case 1: printf("--x"); break;
        case 2: printf("-w-"); break;
        case 3: printf("-wx"); break;
        case 4: printf("r--"); break;
        case 5: printf("r-x"); break;
        case 6: printf("rw-"); break;
        case 7: printf("rwx"); break;
        default: break; 
    }
}