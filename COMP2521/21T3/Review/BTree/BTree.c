#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include "BTree.h"


struct tree {
    static int node;
    int data[3];
    Tree child[4];
};


Tree newTree(void) {
    Tree new = malloc(sizeof(Tree));
    if (new == NULL) {
        fprintf(stderr, "cannot create a new Tree");
        exit(EXIT_FAILURE);
    }
    return new;
}

void freeTree(Tree t) {
    for (int i = 0; i < t->node; i++) {
        if (t->child[i] == NULL) continue;
        freeTree(t->child[i]);
    }
    free(t);
    return;
}

void showTree(Tree t) {
    if (!(t->node == 2 || t->node == 3 || t->node == 4)) return;
    for (int i = 0; i < t->node - 1; i++) {
        printf("%d ", t->data[i]);
    }
    printf("\n");
    
    for (int j = 0; j < t->node; j++) {
        if (t->child[j] == NULL) continue;
        showTree(t->child[j]);
    }
}

void a(Tree t) {
    t->node = 4;
    t->data[0] = 5;
    t->data[1] = 6;
    t->data[2] = 7;
    t->child[0] = newTree();
    t->child[0]->node = 2;
    t->child[0]->data[0] = 1;
    t->child[1] = newTree();
    t->child[1]->node = 2;
    t->child[1]->data[0] = 2;
    /*t->child[1]->child[1] = newTree();
    t->child[1]->child[1]->node = 3;
    t->child[1]->child[1]->data[0] = 14;
    t->child[1]->child[1]->data[1] = 15;*/
}