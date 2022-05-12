// BSTree.h - Interface to binary search tree ADT

#ifndef BSTREE_H
#define BSTREE_H

#define key(tree)   ((tree)->key)
#define left(tree)  ((tree)->left)
#define right(tree) ((tree)->right)

typedef struct node *BSTree;

struct node {
    int key;
    BSTree left;
    BSTree right;
};

// Creates a new empty BSTree
BSTree BSTreeNew(void);

// Frees all memory associated with a BSTree
void BSTreeFree(BSTree t);

// Inserts a new key into a BSTree
BSTree BSTreeInsert(BSTree t, int k);

// Displays a BSTree
void BSTreeShow(BSTree t);

// Creates a BSTree by reading integer values from a line
BSTree BSTreeRead(char *line);

#endif

