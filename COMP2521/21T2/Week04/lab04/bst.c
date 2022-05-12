// bst.c ... client for BSTree ADT

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "BSTree.h"

#define MAXVALS 1000

int main(void) {
	setbuf(stdout, NULL);

	// Build BST from values in stdin
	BSTree t = BSTreeNew();
	int nvals = 0;
	int v[MAXVALS];
	
	int n;
	while (nvals < MAXVALS && scanf("%d", &n) == 1) {
		v[nvals++] = n;
		t = BSTreeInsert(t, n);
	}

	// Display information about constructed tree
	printf("Tree:\n");
	BSTreePrint(t);
	printf("\n");
	printf("#nodes = %d,  ", BSTreeNumNodes(t));
	printf("#leaves = %d\n", BSTreeNumLeaves(t));

	printf("Infix  : "); BSTreeInfix(t);      printf("\n");
	printf("Prefix : "); BSTreePrefix(t);     printf("\n");
	printf("Postfix: "); BSTreePostfix(t);    printf("\n");
	printf("ByLevel: "); BSTreeLevelOrder(t); printf("\n");

	// Check correctness of tree
	// Every inserted value can be found
	for (int i = 0; i < nvals; i++) {
		assert(BSTreeFind(t, v[i]) != 0);
	}

	BSTreeFree(t);
}

