// diary.c

// include required header files
#include <stdio.h>
#include <stdlib.h>

#define MAX_NUM 100


int main(int argc, char *argv[]) {
    char diaryPath[MAX_NUM];
    char *homePath = getenv("HOME");

    snprintf(diaryPath, 100, "%s/.diary", homePath);

    FILE *diaryPtr;
    diaryPtr = fopen(diaryPath, "a");

    for(int i = 1; i < argc; i++) {
        fprintf(diaryPtr, "%s ", argv[i]);
    }

    fprintf(diaryPtr, "%s", "\n");
    return 0;
}