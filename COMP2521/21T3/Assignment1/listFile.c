// COMP2521 Assignment 1

// !!! DO NOT MODIFY THIS FILE !!!

#include <stdio.h>
#include <stdlib.h>

#include "FileType.h"

#define BLUE "\033[34m"
#define RESET_COLOR "\033[0m"

void listFile(char *name, FileType type) {
    char *color = RESET_COLOR;
#ifdef COLORED
    switch (type) {
        case REGULAR_FILE:  color = RESET_COLOR; break;
        case DIRECTORY:     color = BLUE;        break;
        default:            color = RESET_COLOR; break;
    }
#endif
    printf("%s%s%s", color, name, RESET_COLOR);
}

