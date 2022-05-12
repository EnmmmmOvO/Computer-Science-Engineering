// Main program for testing bstToArrays

// !!! DO NOT MODIFY THIS FILE !!!

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "BSTree.h"

void bstToArrays(BSTree t, char keys[], int parents[], int leftSiblings[]);

int main(int argc, char *argv[]) {
	char buffer[1024];

	char *line1 = fgets(buffer, sizeof(buffer), stdin);
	BSTree t = getBST(line1);
	printf("\nDisplaying tree (sideways) \n");
	showBSTree(t);

	int sizeBST = BSTreeNumNodes(t);

	char keys[sizeBST];
	int parents[sizeBST];
	int leftSiblings[sizeBST];

	printf("\n -------  \n");
	bstToArrays(t, keys, parents, leftSiblings);

	fprintf(stdout, "keys:\n");
	for (int i = 0; i < sizeBST; i++) {
		fprintf(stdout, " %c ", keys[i]);
	}
	fprintf(stdout, "\n");

	fprintf(stdout, "parents:\n");
	for (int i = 0; i < sizeBST; i++) {
		fprintf(stdout, "%2d ", parents[i]);
	}
	fprintf(stdout, "\n");

	fprintf(stdout, "leftSiblings:\n");
	for (int i = 0; i < sizeBST; i++) {
		fprintf(stdout, "%2d ", leftSiblings[i]);
	}
	fprintf(stdout, "\n");

	printf(" -------  \n");

	freeBSTree(t);

	return 0;
}

