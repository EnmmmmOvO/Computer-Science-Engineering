#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include "BsTree.h"

struct tree {
    int value;
    Tree left;
    Tree right;
};

Tree newTree(int val) {
    Tree new = malloc(sizeof(Tree));
    if (new == NULL) {
        fprintf(stderr, "malloc memory unsucess!\n");
        exit(EXIT_FAILURE);
    }
    new->value = val;
    new->right = NULL;
    new->left = NULL;
    return new;
}

void freeTree(Tree t) {
    if (t == NULL) return;
    freeTree(t->left);
    freeTree(t->right);
    free(t);
}

void showTree(Tree t) {
    if (t == NULL) return;
    printf("%d\n", t->value);
    showTree(t->left);
    showTree(t->right);
    
}

bool TreeSearch(Tree t, int val) {
    if (t == NULL) {
        return false;
    } else if (t->value == val) {
        return true;
    } else if (t->value > val) {
        return TreeSearch(t->left, val);
    } else {
        return TreeSearch(t->right, val);
    }
}

int  TreeHeight(Tree t) {
    if (t != NULL) {
        int leftTreeHeight = TreeHeight(t->left);
        int rightTreeHeight = TreeHeight(t->right);
        return leftTreeHeight > rightTreeHeight ? leftTreeHeight + 1 : rightTreeHeight + 1;
    } else {
        return 0;
    }
}

int  TreeNumNodes(Tree t) {
    if (t == NULL)
        return 0;
   else
        return 1 + TreeNumNodes(t->left) + TreeNumNodes(t->right);
}

Tree TreeInsert(Tree t, int val) {
    if (t == NULL) {
        return newTree(val);
    } else if (t->value == val) {
        return t;
    } else {
        if (val < t->value) {
            t->left = TreeInsert(t->left, val);
        } else if (val > t->value) {
            t->right = TreeInsert(t->right, val);
        }

        int heightDiff = TreeHeight(t->left) -  TreeHeight(t->right);
        if (heightDiff > 1) {
            if (val > t->left->value) 
                t->left = rotateLeft(t->left);
            t = rotateRight(t);
        } else if (heightDiff * (-1) > 1) {
            if (val < t->right->value) 
                t->right = rotateRight(t->right);
            t = rotateLeft(t);
        }
    }
    return t;
}

Tree TreeDelete(Tree t, int val) {
    if (t == NULL) {
        return t;
    } else if (t->value == val) {
        Tree temp;
        if (t->left == NULL && t->right == NULL) {
            temp = NULL;
        } else if (t->left == NULL) {
            temp = t->right;
        } else if (t->right == NULL) {
            temp = t->left;
        } else {
            temp = t->right;
            for (; temp->left != NULL; temp = temp->left);
            temp->left = t->left;
            temp = t->right;
        }
        free(t);
        return temp;
    } else {
        if (val < t->value) {
            t->left = TreeDelete(t->left, val);
        } else if (val > t->value) {
            t->right = TreeDelete(t->right, val);
        }
        int heightDiff = TreeHeight(t->left) -  TreeHeight(t->right);
        if (heightDiff > 1) {
            if (TreeHeight(t->left->left) <= TreeHeight(t->left->right)) 
                t->left = rotateLeft(t->left);
            t = rotateRight(t);
        } else if (heightDiff * (-1) > 1) {
            if (TreeHeight(t->right->left) >= TreeHeight(t->right->right)) 
                t->right = rotateRight(t->right);
            t = rotateLeft(t);
        }
    }
    return t;
}

Tree rotateRight(Tree t) {
    Tree temp = t->left;
    t->left = temp->right;
    temp->right = t;
    return temp;
}

Tree rotateLeft(Tree t) {
    Tree temp = t->right;
    t->right = temp->left;
    temp->left = t;
    return temp;
}

Tree insertAtRoot(Tree t, int val) {
    if (val == t->value) return t;
    Tree root = newTree(val);
    if (val < t->value) {
        root->right = t;
    } else {
        root->left = t;
    }
    return root;
}

Tree partition(Tree t, int val) {   
    if (t != NULL) {
        int m = TreeNumNodes(t->left);
        if (val < m) {
            t->left = partition(t->left, val);
            t = rotateRight(t);
        } else if (val > m) {
            t->right = partition(t->right, val - m - 1);
            t = rotateLeft(t);
      }
   }
   return t;
}

Tree rebalance(Tree t) {
    int n = TreeNumNodes(t);
    if (n >= 3) {
        t = partition(t, n/2);           // put node with median key at root
        t->left = rebalance(t->left);    // then rebalance each subtree
        t->right = rebalance(t->right);
    }
    return t;
}

