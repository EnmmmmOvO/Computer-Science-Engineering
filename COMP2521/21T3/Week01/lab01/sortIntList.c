// sortIntList.c - a program for testing IntListSortedCopy

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "IntList.h"

int main(int argc, char *argv[]) {
	bool verbose = (argc == 2 && strcmp(argv[1], "-v") == 0);

	// read in the list
	IntList list = IntListRead(stdin);
	if (verbose) {
		printf("Original:\n");
		IntListShow(list);
	}

	assert(IntListOK(list));

	// make a sorted copy of the list
	IntList sortedList = IntListSortedCopy(list);
	IntListFree(list);

	if (verbose) printf("Sorted:\n");
	IntListShow(sortedList);

	// make sure the list is consistent/sorted
	bool ok = IntListOK(sortedList);
	bool sorted = IntListIsSorted(sortedList);
	IntListFree(sortedList);

	if (!ok) {
		fprintf(stderr, "error: the list is not consistent - "
		                "please make sure that you have correctly "
		                "updated the fields of the IntListRep struct\n");
		exit(EXIT_FAILURE);
	} else if (!sorted) {
		fprintf(stderr, "error: the list is not actually sorted\n");
		exit(EXIT_FAILURE);
	}
}

