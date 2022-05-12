#include <stdio.h>
#include <stdlib.h>
#include "Maze.h"

int main (int argc, char *argv[]) {
    if (argc != 2) {
        printf("Please enter the number of vertices!\n");
        exit(EXIT_FAILURE);
    }
    int v = strtol(argv[1], NULL, 10);
    Graph g = newGraph(v);
    Edge e;
    
    int number1;
    while ((scanf("%d", &number1) != 1)) {
        int number2;
        int number3;
        scanf("%d", &number2);
        scanf("%d", &number3);
        e.v = number2;
        e.w = number3;
        if (number1 == 0) {    
            insertEdge(g, e);
        } else if (number1 == 1) {
            removeEdge(g,e);
        }
    }
    showEdges(g);
    return 0;
}