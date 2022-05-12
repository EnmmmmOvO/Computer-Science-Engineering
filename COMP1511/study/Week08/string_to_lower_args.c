#include <stdio.h>
#include <ctype.h>
#include <string.h>



int main (int argc, char *argv[]) {
    if (argc < 2) {
        printf("Nothing can be converted\n");
        return 1;
    }

    for (int loopA = 1; loopA < argc; loopA ++) {
        for (int loopB = 0; loopB < strlen(argv[loopA]); loopB ++) {
            if (argv[loopA][loopB] >= 'A' && argv[loopA][loopB] <= 'Z') {
                printf("%c", argv[loopA][loopB] + 32);
            } else {
                printf("%c", argv[loopA][loopB]);
            }
        }
        printf(" ");
    }
    printf("\n");
   return 0; 
}

