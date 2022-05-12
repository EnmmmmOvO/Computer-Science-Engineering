/*
 Binary Search BSTree ADT implementation 
*/

// !!! DO NOT MODIFY THIS FILE !!!

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "BSTree.h"

/*
#define key(tree)  ((tree)->key)
#define left(tree)  ((tree)->left)
#define right(tree) ((tree)->right)

typedef struct Node {
   char  key;
   BSTree left, right;
} Node;
*/


// make a new node containing key
BSTree newNode(char k) {
   BSTree new = malloc(sizeof(Node));
   assert(new != NULL);
   key(new) = k ;
   left(new) = right(new) = NULL;
   return new;
}

// create a new empty BSTree
BSTree newBSTree() {
   return NULL;
}

// free memory associated with BSTree
void freeBSTree(BSTree t) {
   if (t != NULL) {
      freeBSTree(left(t));
      freeBSTree(right(t));
      free(t);
   }
}

// display BSTree sideways
void showBSTreeR(BSTree t, int depth) {
   if (t != NULL) {
      showBSTreeR(right(t), depth+1);
      int i;
      for (i = 0; i < depth; i++)
	  putchar('\t');            // TAB character
      printf("%c\n", key(t));
      showBSTreeR(left(t), depth+1);
   }
}

void showBSTree(BSTree t) {
   showBSTreeR(t, 0);
}


// count #nodes in BSTree
int BSTreeNumNodes(BSTree t) {
   if (t == NULL)
      return 0;
   else
      return 1 + BSTreeNumNodes(left(t)) + BSTreeNumNodes(right(t));
}

// insert a new key into a BSTree
BSTree BSTreeInsert(BSTree t, char k) {
   if (t == NULL)
      t = newNode(k );
   else if (k < key(t))
      left(t) = BSTreeInsert(left(t), k );
   else if (k > key(t))
      right(t) = BSTreeInsert(right(t), k );
   return t;
}


BSTree  getBST(char *line){

	char delim[] = ", ";
	char key;

	BSTree t = newBSTree(); 

	char *tkn = strtok(line, delim);

	while (tkn != NULL) {
		//printf("'%s'\n", tkn);
		int count = sscanf(tkn, "%c", &key) ;
		if(count == 1) {
			t = BSTreeInsert(t, key) ;
		}
			
		tkn = strtok(NULL, delim);
	}

	return t;
}


