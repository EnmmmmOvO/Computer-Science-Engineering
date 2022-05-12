// Program to test the CentralityMeasures API
// COMP2521 Assignment 2

// !!! DO NOT MODIFY THIS FILE !!!

#include <stdio.h>
#include <stdlib.h>

#include "CentralityMeasures.h"
#include "Graph.h"
#include "GraphRead.h"

#define BUFF_SIZE 1024

static void printUsage(void);
static void displayNodeValuesStruct(NodeValues nvs);

int main(int argc, char *argv[]) {
	if (argc != 3) {
		printUsage();
		return EXIT_FAILURE;
	}

	NodeValues (*fn)(Graph) = NULL;

	Graph g = readGraph(argv[1]);

	if (argv[2][0] == 'c' && argv[2][1] == '\0') {
		fn = closenessCentrality;
	} else if (argv[2][0] == 'b' && argv[2][1] == '\0') {
		fn = betweennessCentrality;
	} else if (argv[2][0] == 'b' && argv[2][1] == 'n' ) {
		fn = betweennessCentralityNormalised;
	} else {
		printUsage();
	}

	if (fn != NULL) {
		NodeValues nvs = fn(g);
		displayNodeValuesStruct(nvs);
		freeNodeValues(nvs);
	}

	GraphFree(g);
}

static void printUsage(void) {
	printf("Usage: ./testCentralityMeasures [file] [flag]\n");
	printf("Valid Flags:\n");
	printf("    c    : closeness centrality\n");
	printf("    b    : betweenness centrality\n");
	printf("    bn   : betweenness centrality normalised\n");
}

static void displayNodeValuesStruct(NodeValues nvs) {
	int i = 0;
	for (i = 0; i < nvs.numNodes; i++) {
		printf("%d: %lf\n", i, nvs.values[i]);
	}
}

