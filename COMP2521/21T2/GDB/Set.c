// Set ADT implementation using a binary search tree

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "Set.h"

typedef struct node *Node;
struct node {
	int  elem;
	Node left;
	Node right;
};

struct set {
	Node root;
	int  size;
};

static void doSetFree(Node n);
static Node doSetAdd(Node n, int elem);
static Node newNode(int elem);
static void doSetPrint(Node n);

/**
 * Creates a new empty set
 */
Set  SetNew(void) {
	Set s = malloc(sizeof(Set));
	if (s == NULL) {
		fprintf(stderr, "couldn't allocate set\n");
		exit(EXIT_FAILURE);
	}
	
	return s;
}

/**
 * Frees all resources associated with the given set
 */
void SetFree(Set s) {
	doSetFree(s->root);
	free(s);
}

static void doSetFree(Node n) {
	Node p = n;
	while (n != NULL) {
		p = n;
		n = n->right;
		free(p);
	}
}

/**
 * Adds an element to the given set
 * Does not insert duplicates
 */
void SetAdd(Set s, int elem) {
	s->root = doSetAdd(s->root, elem);
	Node n = s->root;
	s->size = 0;
	for (s->size = 0; n != NULL; n = n->right, s->size ++);
}

static Node doSetAdd(Node n, int elem) {
	if (n == NULL) {
		return newNode(elem);
	}
	
	Node p = n;
	Node s = newNode(elem);

	if (elem < p->elem) {
		p->left = s;
		s->right = p;
		n = s; 
	} else if (elem > p->elem) {
		while (elem >= p->elem || p->right != NULL) {
			p = p->right;
			if (elem == p->elem) {
				free(s);
				return n;
			}

			if (p->right == NULL) 
				break;
		}

		if (p->right == NULL) {
			p->right = s;
			s->left = p;
		} else {
			p->left->right = s;
			s->left = p->left;
			s->right = p;
			p->left = s;
		}
	} else {
		free(s);
	}
	return n;
}

static Node newNode(int elem) {
	Node n = malloc(sizeof(struct node));
	if (n == NULL) {
		fprintf(stderr, "couldn't allocate node\n");
		exit(EXIT_FAILURE);
	}
	
	n->left = NULL;
	n->right = NULL;
	n->elem = elem;
	return n;
}

/**
 * Returns true if the given element is contained in the set, and false
 * otherwise
 */
bool SetContains(Set s, int elem) {
	Node n = s->root;
	
	if (elem < n->elem) {
		return false;
	}
	// iterative search
	while (n != NULL) {
		if (elem == n->elem) {
			return true;
		}
		n = n->right;

	}
	
	return false; // couldn't find element
}

/**
 * Returns the size (number of elements) of the given set
 */
int  SetSize(Set s) {
	return s->size;
}

/**
 * Prints the set to stdout
 */
static bool firstElem = true;

void SetPrint(Set s) {
	printf("{");
	
	firstElem = true;
	doSetPrint(s->root);
	
	printf("}\n");
}

static void doSetPrint(Node n) {
	if (n == NULL) return;
	
	// print comma before each element except the first
	if (!firstElem) {
		printf(", ");
	}
	printf("%d", n->elem);
	firstElem = false;
	
	doSetPrint(n->right);
}

