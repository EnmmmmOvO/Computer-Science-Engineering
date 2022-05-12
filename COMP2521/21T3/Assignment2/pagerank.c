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
#include "Graph.h"

void pageRank(Graph g, double d, double diffPR, int maxIterations);

int main(int argc, char *argv[]) {
    if (argc != 4) {
        fprintf(stderr, "the input argument is wrong!\n");
        exit(EXIT_FAILURE);
    }

    double d = atof(argv[1]);
    double diffPR = atof(argv[2]);
    int maxIterations = atoi(argv[3]);

    assert(d > 0 && d < 1);
    assert(diffPR > 0);
    assert(!(maxIterations < 0));

    Graph g = GraphNew();
    
    FILE *collectionFile = fopen("ex1/collection.txt", "r");
    if (collectionFile == NULL) {
        fprintf(stderr, "ex1/collection.txt cannot open\n");
        exit(EXIT_FAILURE);
    }

    char takeLine[MAX_SIZE];
    while (fgets(takeLine, MAX_SIZE, collectionFile) != NULL) {
        if (strcmp(takeLine, "\r\n")) {
            for (int loop = 0; takeLine[loop] != '\0'; loop++) {
                if (takeLine[loop] == ' ') continue;
                if (takeLine[loop] == 'u' && takeLine[loop + 1] == 'r' && takeLine[loop + 2] == 'l') {
                    int loopA = 0;
                    char temp[MAX_SIZE];
                    for (loop += 3; takeLine[loop] != ' ' && takeLine[loop] != '\r'; loop++, loopA++)
                        temp[loopA] = takeLine[loop];
                    GraphUrlInsert(g, temp);
                    continue;
                }
                if (takeLine[loop] == '\r' && takeLine[loop] == '\n') break;
            }
        }
    }

    fclose(collectionFile);

    for (int loop = 0; loop < GraphNumVertices(g); loop++) {
        char *code = getUrlCode(g, loop);
        char address[MAX_SIZE] = "ex1/url";
        strcat(address, code);
        strcat(address, ".txt");
        FILE *urlContent = fopen(address, "r");
        if (urlContent == NULL) {
            fprintf(stderr, "%s cannot open\n", address);
            exit(EXIT_FAILURE);
        }
        int temp = 0;
        while (fgets(takeLine, MAX_SIZE, urlContent) != NULL) {
            if (strcmp(takeLine, "#start Section-1\r\n") == 0) {
                temp = 1; 
                continue;
            } else if (strcmp(takeLine, "#end Section-1\r\n") == 0) {
                temp = 0;
                continue;
            } else if (strcmp(takeLine, "#start Section-2\r\n") == 0) {
                temp = 2;
                continue;
            } else if (strcmp(takeLine, "#end Section-2\r\n") == 0) {
                temp = 0;
                continue;
            }

            if (temp == 1) {
                if (strcmp(takeLine, "\r\n")) {
                    for (int loopPosition = 0; takeLine[loopPosition] != '\0'; loopPosition++) {
                        if (takeLine[loopPosition] == ' ') continue;
                        if (takeLine[loopPosition] == 'u' && takeLine[loopPosition + 1] == 'r' && takeLine[loopPosition + 2] == 'l') {
                            int loopCode = 0;
                            char tempCode[MAX_SIZE];
                            for (loopPosition += 3; takeLine[loopPosition] != ' ' && takeLine[loopPosition] != '\r'; loopPosition++, loopCode++)
                                tempCode[loopCode] = takeLine[loopPosition];
                            
                            UrlLink(g, loop, tempCode);
                            continue;
                        }
                        if (takeLine[loop] == '\r' && takeLine[loop] == '\n') break;
                    }
                }    
            } else if (temp == 2) {
                if (strcmp(takeLine, "\r\n")) {
                    UrlContentInsert(g, loop, takeLine);
                }
            }
            
        }
        fclose(urlContent);
    }

    pageRank(g, d, diffPR, maxIterations);
    GraphFree(g);
}

void pageRank(Graph g, double d, double diffPR, int maxIterations) {
    int N = GraphNumVertices(g);
    int iteration = 0;
    setWeight(g, 1.0/N);
    double diff = diffPR;
    int t;
    while (iteration < maxIterations && !(diff < diffPR)) {
        t = iteration;
        diff = changeWeight(g, t, d);
        iteration++;
    }
    printWeight(g, t + 1);
}

