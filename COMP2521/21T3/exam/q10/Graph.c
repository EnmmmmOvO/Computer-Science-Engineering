// Implementation of the directed graph ADT using an adjacency matrix

// !!! DO NOT MODIFY THIS FILE !!!

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "Graph.h"

/*
typedef struct GraphRep {
    int **edges; // adjacency matrix
    int   nV;    // #vertices
    int   nE;    // #edges
} GraphRep;
*/

static bool validV(Graph g, Vertex v);

Graph GraphNew(int nV) {
    assert(nV > 0);

    Graph g = malloc(sizeof(*g));
    assert(g != NULL);
    g->nV = nV;
    g->nE = 0;

    // allocate memory for each row
    g->edges = malloc(nV * sizeof(int *));
    assert(g->edges != NULL);

    // allocate memory for each column and initialise with 0
    for (int i = 0; i < nV; i++) {
        g->edges[i] = calloc(nV, sizeof(int));
        assert(g->edges[i] != NULL);
    }

    return g;
}

void GraphFree(Graph g) {
    assert(g != NULL);

    for (int i = 0; i < g->nV; i++) {
        free(g->edges[i]);
    }
    free(g->edges);
    free(g);
}

void GraphInsertEdge(Graph g, Vertex from, Vertex to) {
    assert(validV(g, from) && validV(g, to));

    if (!g->edges[from][to]) {
        g->edges[from][to] = 1;
        g->nE++;
    }
}

bool GraphIsAdjacent(Graph g, Vertex v, Vertex w) {
    assert(validV(g, v) && validV(g, w));

    return (g->edges[v][w] != 0);
}

void GraphShow(Graph g) {
    assert(g != NULL);
    
    printf("Number of vertices: %d\n", g->nV);
    printf("Number of edges: %d\n", g->nE);
    for (int i = 0; i < g->nV; i++) {
        for (int j = 0; j < g->nV; j++) {
            if (g->edges[i][j]) {
                printf("Edge %d -> %d\n", i, j);
            }
        }
    }
}

// Checks if a vertex is valid in a graph
static bool validV(Graph g, Vertex v) {
    return (v >= 0 && v < g->nV);
}

