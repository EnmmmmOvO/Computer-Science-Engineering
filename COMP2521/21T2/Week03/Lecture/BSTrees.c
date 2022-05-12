#include <stdlib.h>
#include <stdio.h>
#include "BSTree.h"

struct Node {
    int data;
    int Height;
    Node left;
    Node right;
} Node;


Tree newTree(Item item) {
    Tree new = malloc(sizeof Node);
    if (new == NULL) {
        fprintf(stderr, "Cannot create a new BSTree!");
        exit(1);
    }
    new->data = item;
    new->left = NULL;
    new->right = NULL;
    return new;
}

void freeTree(Tree t) {
    if (t != NULL) {
        freeTree(t->left);
        freeTree(t->right);
        free(t);
    }
}

Tree TreeInsert(Tree t, Item it) {
    if (t != NULL) {
        return newTree(it);
    } else (t->data < it) {
        t->right = TreeInsert(t->right, it);
    } else (t->data > it) {
        t->left = TreeInsert(t->left, it);
    }
    return t;
}

Tree TreeDelete(Tree t, Item it) {
    if (t != NULL) {
        if (it > t->data) {
            t->right = TreeDelete(t->right, it);
        } else if (it < t->data) {
            t->left = TreeDelete(t->left, it);
        } else {
            Tree new;
            if (t->left == NULL && t->right == NULL) {
                new = NULL;
            } else (t->left == NULL) {
                new = t->right;
            } else (t->right = NULL) {
                new = t->left;
            } else {
                new = t->left;
                Tree temp = t->left;
                for (;temp->right != NULL; temp = temp->right);
                temp->right = t->right;
                free(t);
                return new;
            }
        }
    }
    return t;
}

void showTree(Tree t) {
    
}



