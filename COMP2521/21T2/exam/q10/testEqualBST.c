// testEqualBST.c

#include <stdio.h>
#include <stdlib.h>

#include "BSTree.h"

int equalBST(BSTree t1, BSTree t2);

int main(int argc, char *argv[]) {
    char buffer[1024];

    char *line1 = fgets(buffer, sizeof(buffer), stdin);
    BSTree t1 = BSTreeRead(line1);
    printf("t1:\n\n");
    BSTreeShow(t1);
    printf("\n");

    char *line2 = fgets(buffer, sizeof(buffer), stdin);
    BSTree t2 = BSTreeRead(line2);
    printf("t2:\n\n");
    BSTreeShow(t2);
    printf("\n");
    
    int res = equalBST(t1, t2);
    printf("equalBST returned: %d\n", res);
    
    BSTreeFree(t1);
    BSTreeFree(t2);
}

