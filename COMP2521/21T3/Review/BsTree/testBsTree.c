#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include "BsTree.h"


int main (int argc, char *argv[]) {
    Tree t = newTree(50);
    t = TreeInsert(t, 25);
    t = TreeInsert(t, 51);
    t = TreeInsert(t, 10);
    t = TreeInsert(t, 30);
    t = TreeInsert(t, 100);
    t = TreeInsert(t, 2);
    t = TreeInsert(t, 11);
    t = TreeInsert(t, 28);
    t = TreeInsert(t, 35);
    t = TreeDelete(t, 100);

    //t = rebalance(t);
    showTree(t);
    freeTree(t);

}