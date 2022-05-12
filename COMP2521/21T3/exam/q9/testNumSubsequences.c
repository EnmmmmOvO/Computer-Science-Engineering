// Main program for testing numSubsequences

// !!! DO NOT MODIFY THIS FILE !!!

#include <stdio.h>
#include <stdlib.h>

#include "list.h"

int numSubsequences(List listA, List listB, int tolerance);

int main(int argc, char *argv[]) {
    char buffer[1024];

    char *line1 = fgets(buffer, sizeof(buffer), stdin);
    List listA = ListRead(line1);
    printf("List A: ");
    ListShow(listA);

    char *line2 = fgets(buffer, sizeof(buffer), stdin);
    List listB = ListRead(line2);
    printf("List B: ");
    ListShow(listB);

	int tolerance;
	scanf("%d", &tolerance);
	printf("Tolerance: %d\n", tolerance);

    int ans = numSubsequences(listA, listB, tolerance);
    printf("numSubsequences returned: %d\n", ans);

    ListFree(listA);
    ListFree(listB);
}

