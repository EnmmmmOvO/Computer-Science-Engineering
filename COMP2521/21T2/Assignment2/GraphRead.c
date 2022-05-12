// Function to read in a graph
// COMP2521 Assignment 2

// !!! DO NOT MODIFY THIS FILE !!!

#include "Graph.h"
#include "GraphRead.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

Graph readGraph(char *file) {
	FILE *fp = fopen(file, "r");
	if (fp == NULL) {
		fprintf(stderr, "error: couldn't open %s for reading\n", file);
		exit(EXIT_FAILURE);
	}

	int nV = 0;
	if (fscanf(fp, "%d", &nV) != 1) {
		fprintf(stderr, "error: failed to read number of vertices\n");
		exit(EXIT_FAILURE);
	}
	
	Graph g = GraphNew(nV);
	
	int v, w;
	int weight;
	while (fscanf(fp, "%d,%d,%d", &v, &w, &weight) == 3) {
		GraphInsertEdge(g, v, w, weight);
	}

	fclose(fp);
	return g;
}

