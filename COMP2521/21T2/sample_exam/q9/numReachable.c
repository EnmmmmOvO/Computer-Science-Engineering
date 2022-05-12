
#include <stdio.h>
#include <stdlib.h>

#include "Graph.h"

typedef struct node *Node;

struct node {
	int data;
	Node next;
};

Node newNode(int src);

int numReachable(Graph g, int src) {
	int total = 1;
	int nV = GraphNumVertices(g);
	int array[1000] = {0};
	array[src] = -1;
	Node n = newNode(src);
	while (n != NULL) {
		for (int loop = 0; loop < nV; loop++) {
			if (GraphIsAdjacent(g, loop, n->data) == 1 && array[loop] == 0) {
				Node new = newNode(loop);
				Node q;
				for (q = n; q->next != NULL; q = q->next);
				q->next = new;
				array[loop] = -1;
				total++;
			}
		}
		Node p = n;
		n = n->next;
		free(p);
	}
	// TODO
	return total;
}

Node newNode(int src) {
	Node n = malloc(sizeof *n);
	n->next = NULL;
	n->data = src;
	return n;
}

