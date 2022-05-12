// Main program for testing findPopularFollowers

// !!! DO NOT MODIFY THIS FILE !!!

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "Graph.h"

void findPopularFollowers(Graph g, int src, int *followers);

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

	int *followers = malloc(nV * sizeof(int));
	assert(followers != NULL);
	int i;
	for (i = 0; i < nV; i++) {
		followers[i] = -1.0;
	}

	findPopularFollowers(g, src, followers); 

	printf("Popular followers of node %d:\n", src);
	for (i = 0; i < nV; i++) {
		if (followers[i] == 1) {
			printf(" node %d\n", i);
		}
	}
	printf("\n");

	free(followers);
	GraphFree(g);
}

