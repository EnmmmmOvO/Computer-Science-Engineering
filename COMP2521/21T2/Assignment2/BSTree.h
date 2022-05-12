// Binary Search Tree ADT interface
// COMP2521 Assignment 2

// !!! DO NOT MODIFY THIS FILE !!!

#ifndef BSTREE_H
#define BSTREE_H

typedef int Item;

typedef struct Node *Tree;

Tree TreeNew(void);

void TreeFree(Tree);

Tree TreeGetLeft(Tree t);

Tree TreeGetRight(Tree t);

Tree TreeInsert(Tree, Item);

void TreePrint(Tree t);

Tree TreeAdd(Tree t1, Tree t2);

#endif

