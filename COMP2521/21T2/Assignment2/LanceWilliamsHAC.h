// Lance-Williams Algorithm for Hierarchical Agglomerative Clustering
// COMP2521 Assignment 2

// !!! DO NOT MODIFY THIS FILE !!!

#ifndef LANCE_WILLIAMS_HAC_H
#define LANCE_WILLIAMS_HAC_H

#include <stdbool.h>

#include "Graph.h"

#define SINGLE_LINKAGE   1
#define COMPLETE_LINKAGE 2

typedef struct DNode *Dendrogram;
typedef struct DNode {
	int vertex; // This value is irrelevant in non-leaf dendrogram nodes
	            // (see the example in the Excel file, linked in spec)
	Dendrogram left;
	Dendrogram right;
} DNode;

/**
 * Generates  a Dendrogram using the Lance-Williams algorithm (discussed
 * in the spec) for the given graph  g  and  the  specified  method  for
 * agglomerative  clustering. The method can be either SINGLE_LINKAGE or
 * COMPLETE_LINKAGE (you only need to implement these two methods).
 *
 * The function returns a 'Dendrogram' structure.
 */
Dendrogram LanceWilliamsHAC(Graph g, int method);

/**
 * Frees all memory associated with the given Dendrogram structure.
 */
void freeDendrogram(Dendrogram d);

#endif

