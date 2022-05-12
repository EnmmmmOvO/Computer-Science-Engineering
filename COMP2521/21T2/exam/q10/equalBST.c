// equalBST.c ... implementation of equalBST function

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "BSTree.h"

int equalBST(BSTree t1, BSTree t2) {
    if (t1 == NULL && t2 == NULL) return 1;
    if (t1 == NULL && t2 != NULL) return 0;
    if (t1 != NULL && t2 == NULL) return 0;
    if (t1->key != t2->key) return 0;
    return equalBST(t1->left, t2->left) && equalBST(t1->right, t2->right);
}

