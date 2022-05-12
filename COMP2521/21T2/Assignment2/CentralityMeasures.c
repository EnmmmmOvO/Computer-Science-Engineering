// Centrality Measures API implementation
// COMP2521 Assignment 2

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "CentralityMeasures.h"
#include "Dijkstra.h"
#include "Graph.h"
#include "PQ.h"

double Wasserman_Faust_formula(double total, int n, int N) {
	return (n - 1) * (n - 1) / (total * (N - 1));
}

NodeValues closenessCentrality(Graph g) {
	NodeValues nvs = {0};
	int nV = g->nV;
	for (int loop = 0; loop < nV; loop++) {
		ShortestPaths sps  = dijkstra(g, loop);
		double total = 0.0;
		for (int loopA = 0; loopA < nV; loopA++) {
			if (sps.dist[loopA] != INFINITY && loopA != loop) 
				total = total + sps.dist[loopA];
 		}
		nvs.values[loop] = 1 / total;
		nvs.numNodes ++;
	}
	return nvs;
}

NodeValues betweennessCentrality(Graph g) {
	NodeValues nvs = {0};

	int nV = g->nV;
	for (int loop = 0; loop < nV; loop++) {
		ShortestPaths sps  = dijkstra(g, loop);
		double total = 0.0;
		for (int loopA = 0; loopA < nV; loopA++) {
			if (sps.dist[loopA] != INFINITY) 
				total = total + sps.dist[loopA];
 		}
		nvs.values[loop] = Wasserman_Faust_formula(total, loop, nV);
		nvs.numNodes ++;
	}
	return nvs;
}

NodeValues betweennessCentralityNormalised(Graph g) {
	NodeValues nvs = {0};
	return nvs;
}


void showNodeValues(NodeValues nvs) {

}

void freeNodeValues(NodeValues nvs) {

}

