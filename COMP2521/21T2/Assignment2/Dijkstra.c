// Dijkstra API implementation
// COMP2521 Assignment 2

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "Dijkstra.h"
#include "Graph.h"
#include "PQ.h"

#define MAX_NUM 1000

PredNode newPred(Vertex t);


ShortestPaths dijkstra(Graph g, Vertex src) {
    // create a new ShortestPaths struct;
    ShortestPaths sps = {0};
    //set src 
    sps.src = src;

    //get the number of Vertices
    int nV = GraphNumVertices(g);
    //set the initial distance to src is INFINITY
    for (int loop = 0; loop < GraphNumVertices(g); loop++) {
        sps.dist[loop] = INFINITY;
        sps.pred[src] = NULL;
    }
    //the distance between src and itself is 0
    sps.dist[src] = 0;
    sps.pred[src] = NULL;

    PQ pq = PQNew();
    PQInsert(pq, src, 0);
    
    for (int loop = 0; loop < nV; loop ++) {
        AdjList l = GraphOutIncident(g, src);
        int temp = sps.dist[loop];

        while (l != NULL) {
            if (sps.dist[l->v] == INFINITY) {
                sps.dist[l->v] = l->weight + temp;
                PredNode p = newPred(loop);
                sps.pred[l->v] = p;
            } else {
                if (sps.dist[l->v] > (temp + l->weight)) {
                    sps.dist[l->v] = l->weight + temp;
                    sps.pred[l->v]->v = loop;
                } else if (sps.dist[l->v] == (temp + l->weight)) {
                    PredNode p = newPred(loop);
                    sps.pred[l->v]->next = p;
                }
            }
            l = l->next;
        }
    }
    return sps;
}


PredNode newPred(Vertex t) {
    PredNode np = malloc(sizeof(PredNode));
    np->v = t;
    np->next = NULL;
    return np;
}

void showShortestPaths(ShortestPaths sps) {

}

void freeShortestPaths(ShortestPaths sps) {

}

