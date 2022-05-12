
#ifndef PLACE_H
#define PLACE_H

#include <stdbool.h>

#define MAX_PLACE_NAME 31

typedef struct place {
    char name[MAX_PLACE_NAME + 1];
    int  x;
    int  y;
} Place;

typedef struct powerLine {
    Place p1;
    Place p2;
} PowerLine;

#endif
