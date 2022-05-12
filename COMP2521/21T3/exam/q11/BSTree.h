/* Binary Search BSTree ADT interface
   Written by Ashesh Mahidadia
*/

// !!! DO NOT MODIFY THIS FILE !!!

#ifndef BSTree_H
#define BSTrees_H

#include <stdbool.h>

/* External view of BSTree (key is of type char)
   To simplify this exam setup, we are exposing the
   following types to a client.
*/

#define key(tree)  ((tree)->key)
#define left(tree)  ((tree)->left)
#define right(tree) ((tree)->right)

typedef char Key;

typedef struct Node *BSTree;
typedef struct Node {
	char  key;
	BSTree left, right;
} Node;


BSTree newBSTree();        // create an empty BSTree
void freeBSTree(BSTree);   // free memory associated with BSTree
void showBSTree(BSTree);   // display a BSTree (sideways)
BSTree BSTreeInsert(BSTree, Key);   // insert a new key into a BSTree
int BSTreeNumNodes(BSTree t);   // count #nodes in BSTree

BSTree getBST(char *line);

#endif

