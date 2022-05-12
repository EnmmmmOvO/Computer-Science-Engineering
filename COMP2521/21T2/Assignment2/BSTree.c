// Binary Search Tree ADT implementation
// COMP2521 Assignment 2

// !!! DO NOT MODIFY THIS FILE !!!

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "BSTree.h"

#define data(tree)  ((tree)->data)
#define left(tree)  ((tree)->left)
#define right(tree) ((tree)->right)

typedef struct Node {
	int  data;
	Tree left;
	Tree right;
} Node;

// make a new node containing data
static Tree newNode(Item it) {
	Tree new = malloc(sizeof(Node));
	assert(new != NULL);
	data(new) = it;
	left(new) = right(new) = NULL;
	return new;
}

Tree TreeNew(void) {
	return NULL;
}

void TreeFree(Tree t) {
	if (t != NULL) {
		TreeFree(left(t));
		TreeFree(right(t));
		free(t);
	}
}

Tree TreeGetLeft(Tree t) {
	if (t == NULL) {
		return NULL;
	}
	return left(t);
}

Tree TreeGetRight(Tree t) {
	if (t == NULL) {
		return NULL;
	}
	return right(t);
}

Tree TreeInsert(Tree t, Item it) {
	if (t == NULL) {
		t = newNode(it);
	} else if (it < data(t)) {
		left(t) = TreeInsert(left(t), it);
	} else if (it > data(t)) {
		right(t) = TreeInsert(right(t), it);
	}
	return t;
}

void TreePrint(Tree t) {
	if (t == NULL) {
		return;
	}

	TreePrint(left(t));

	if (left(t) != NULL) {
		printf(", ");
	}
	printf("%d", data(t));
	if (right(t) != NULL) {
		printf(", ");
	}

	TreePrint(right(t));
}

Tree TreeAdd(Tree t1, Tree t2) {
	if (t2 == NULL) {
		return t1;
	}

	Tree t = TreeInsert(t1, data(t2));
	t = TreeAdd(t, left(t2));
	t = TreeAdd(t, right(t2));
	return t;
}

