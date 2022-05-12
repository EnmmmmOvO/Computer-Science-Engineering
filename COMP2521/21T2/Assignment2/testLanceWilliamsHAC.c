// Program to test the LanceWilliamsHAC API
// COMP2521 Assignment 2

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "BSTree.h"
#include "GraphRead.h"
#include "LanceWilliamsHAC.h"

static Tree printDendrogram(Dendrogram dn, int depth);
static void printClusters(Tree t, int depth);

int main(int argc, char* argv[]) {
	if (argc < 2) {
		printf("Usage: ./testLanceWilliamsHAC [file]\n");
		return EXIT_FAILURE;
	}

	Graph g = readGraph(argv[1]);

	Dendrogram dn = LanceWilliamsHAC(g, SINGLE_LINKAGE);
	Tree allTree = printDendrogram(dn, 1);
	printClusters(allTree, 0);
	TreeFree(allTree);
	freeDendrogram(dn);

	GraphFree(g);
}

static Tree printDendrogram(Dendrogram dn, int depth) {
	// To avoid infinite looping, due to a possible  
	// incorrect logic in the program being tested!
	assert(depth < 200);

	Tree tr = NULL;
	Tree tl = NULL;

	if (dn == NULL) {
		return NULL;
	}

	if (dn->left == NULL && dn->right == NULL) {
		Tree t = TreeNew();
		t = TreeInsert(t, dn->vertex);
		return t;
	}

	if (dn->left != NULL) {
		tl = printDendrogram(dn->left, depth + 1);
		printClusters(tl, depth);
	}

	if (dn->right != NULL) {
		tr = printDendrogram(dn->right, depth + 1);
		printClusters(tr, depth);
	}

	Tree bothTrees = TreeAdd(tl, tr);
	TreeFree(tr);
	return bothTrees;
}

static void printClusters(Tree t, int depth) {
	// To avoid infinite looping, due to a possible  
	// incorrect logic in the program being tested!
	assert(depth < 200);

	printf("%d: {", depth);
	TreePrint(t);
	printf("}");

	if ((TreeGetLeft(t) == NULL) && (TreeGetRight(t) == NULL)) {
		printf(" (leaf)");
	}
	printf("\n");
}

