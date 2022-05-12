// BSTree.h ... interface to binary search tree ADT

#ifndef BSTREE_H
#define BSTREE_H

#include <stdbool.h>

typedef struct BSTNode *BSTree;

////////////////////////////////////////////////////////////////////////

// Creates a new empty BSTree
BSTree BSTreeNew(void);

// Frees all the memory associated with the given BSTree
void BSTreeFree(BSTree t);

// Inserts a new value into the given BSTree and returns the root of the
// updated BSTree. Does not insert duplicate values.
BSTree BSTreeInsert(BSTree t, int v);

// Checks whether a value is in the given BSTree
bool BSTreeFind(BSTree t, int v);

// Displays the given BSTree on stdout
void BSTreePrint(BSTree t);

////////////////////////////////////////////////////////////////////////

// Prints the values in the given BSTree in infix order
void BSTreeInfix(BSTree t);

// Prints the values in the given BSTree in prefix order
void BSTreePrefix(BSTree t);

// Prints the values in the given BSTree in postfix order
void BSTreePostfix(BSTree t);

// Prints the values in the given BSTree in level-order
void BSTreeLevelOrder(BSTree t);

////////////////////////////////////////////////////////////////////////

// Counts the number of nodes in the given BSTree
int BSTreeNumNodes(BSTree t);

// Counts the number of leaves in the given BSTree
int BSTreeNumLeaves(BSTree t);

////////////////////////////////////////////////////////////////////////

#endif

