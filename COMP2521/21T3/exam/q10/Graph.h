// Graph.h - Interface to the directed graph ADT

// !!! DO NOT MODIFY THIS FILE !!!

#ifndef GRAPH_H
#define GRAPH_H

#include <stdbool.h>

typedef struct GraphRep *Graph;

struct GraphRep {
    int **edges; // adjacency matrix
    int   nV;    // #vertices
    int   nE;    // #edges
};

// vertices are ints
typedef int Vertex;

// Create a new graph
Graph GraphNew(int nV);

// Frees all memory associated with the given graph
void GraphFree(Graph g);

// Inserts a directed edge from 's' to 'd'
void GraphInsertEdge(Graph g, Vertex s, Vertex d);

// Returns true if there is an edge from 's' to 'd', false otherwise
bool GraphIsAdjacent(Graph g, Vertex s, Vertex d);

// Prints the given graph to stdout
void GraphShow(Graph g);

#endif

