// COMP2521 Assignment 2

// Written by: Jinghan Wang
// Date:

#include <assert.h>
#include <ctype.h>
#include <math.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_SIZE 100
#include "Word.h"

int main(int argc, char *argv[]) {
    Graph g = GraphNew();
    
    FILE *pagerankList = fopen("ex2/pagerankList.txt", "r");
    if (pagerankList == NULL) {
        fprintf(stderr, "ex2/pagerankList.txt cannot open\n");
        exit(EXIT_FAILURE);
    }

    char takeLine[MAX_SIZE];
    while (fgets(takeLine, MAX_SIZE, pagerankList) != NULL) {
        if (strcmp(takeLine, "\r\n")) {
            char temp[MAX_SIZE];
            int loop = 3;
            for (int loopA = 0; takeLine[loop] != ','; loop++, loopA++) {
                temp[loopA] = takeLine[loop];
            }
            char weight[MAX_SIZE];
            for (;takeLine[loop] != '0' || takeLine[loop + 1] != '.'; loop++);
            for (int loopA = 0; takeLine[loop] != '\r'; loop++, loopA++) {
                weight[loopA] = takeLine[loop];
            }
            inputUrl(g, temp, atof(weight));
        }
    }

    fclose(pagerankList);

    FILE *invertedIndex = fopen("ex2/invertedIndex.txt", "r");
    while (fgets(takeLine, MAX_SIZE, invertedIndex) != NULL) {
        if (strcmp(takeLine, "\r\n")) {
            inputLine(g, takeLine);
        }
    }
    
    fclose(invertedIndex);

    for (int loop = 1; loop <= argc; loop++) {
        search(g, argv[loop]);
    }

    print(g);

    return 0;
}

