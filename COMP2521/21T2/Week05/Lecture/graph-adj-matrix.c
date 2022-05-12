#include "Graph.h"
#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <stdbool.h>

#define CONNECTED 1
#define INCONNECTED 0

typedef struct GraphRep {
    int **edges;
    int nV;
    int nE;
} GraphRep;

Graph GraphNew(int v)
{
    assert(v >= 0);
    
    Graph g = malloc(sizeof(GraphRep));
    g->nV = v;
    g->nE = 0;
   
    g->edges = malloc(v * sizeof(int *));
    assert(g->edges != NULL);
    for (int i = 0; i < v; i ++) {
        g->edges[i] = calloc(v, sizeof(int));
        assert(g->edges[i] != NULL);
    }
    return g;
}

bool validV(Graph g, Vertex v) {
   return (g != NULL && v >= 0 && v < g->nV);
}

void GraphEdgeInsert(Graph g, Edge e) {
    if (g->edges[e.v][e.w] == INCONNECTED) {
       g->edges[e.v][e.w] = CONNECTED;
       g->edges[e.w][e.v] = CONNECTED;
       g->nE ++;
    }
}

void GraphEdgeRemove(Graph g, Edge e) {
    if (g->edges[e.v][e.w] == INCONNECTED) {
        printf("%d and %d is not connected!\n", e.v, e.w);
        return;
    }
    g->edges[e.v][e.w] = INCONNECTED;
    g->edges[e.w][e.v] = INCONNECTED;
    g->nE --;
}

bool GraphAdjacent(Graph g, Vertex v, Vertex w) {
   assert(g != NULL && validV(g,v) && validV(g,w));

   return (g->edges[v][w] != 0);
}

void GraphShow(Graph g) {
    if (g == NULL) {
        return;
    }
    for (int i = 0; i < g->nV; i ++) {
        for (int j = i + 1; j < g->nV; j ++) {
            if (g->edges[i][j] == CONNECTED) printf("%d --- %d\n", i, j);
        }
    }
}

void GraphDestroy(Graph g) {
   assert(g != NULL);

   int i;
   for (i = 0; i < g->nV; i++) {
      free(g->edges[i]);
   }
   free(g->edges);
   free(g);
}



