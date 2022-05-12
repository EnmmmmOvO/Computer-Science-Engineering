// testRankPopularity.c

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "Graph.h"

void rankPopularity(Graph g, int src, double *mnV);

int main(void) {
    int nV;
    if (scanf("nV: %d ", &nV) != 1) {
        printf("error: failed to read nV\n");
        return 1;
    }

    int src;
    if (scanf("src: %d ", &src) != 1) {
        printf("error: failed to read src\n");
        return 1;
    }
    
    printf("nV: %d\nsrc: %d\n\n", nV, src);
    
    Graph g = GraphNew(nV);
    int s, d;
    while (scanf("%d %d", &s, &d) == 2) {
        GraphInsertEdge(g, s, d);
        printf("Edge inserted: %d -> %d\n", s, d);
    }
    printf("\n");

    double *mnV = malloc(nV * sizeof(double));
    assert(mnV != NULL);
    int i;
    for (i = 0; i < nV; i++) {
        mnV[i] = -1.0;
    }

    rankPopularity(g, src, mnV);

    printf("Popularity ranks:\n");
    for (i = 0; i < nV; i++) {
        printf(" node: %d, rank: %10.3lf\n", i, mnV[i]);
    }
    printf("\n");

    free(mnV);
    GraphFree(g);
}

