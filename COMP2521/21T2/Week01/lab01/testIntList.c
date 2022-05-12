// testIntList.c - a program for testing IntListInsertInOrder

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "IntList.h"

#define MAX_LINE_LEN 1024

static IntList readIntList(void);

int main(void) {
	// read the list
	printf("Enter some numbers (must be in ascending order): ");
	IntList l = readIntList();
	if (!IntListIsSorted(l)) {
		fprintf(stderr, "error: the numbers were not ordered\n");
		IntListFree(l);
		exit(EXIT_FAILURE);
	}

	// read the number to be inserted
	printf("Enter number to insert: ");
	int num;
	if (scanf("%d", &num) != 1) {
		fprintf(stderr, "error: failed to read number");
		IntListFree(l);
		exit(EXIT_FAILURE);
	}

	printf("Original list:\n");
	IntListShow(l);

	printf("After inserting %d:\n", num);
	IntListInsertInOrder(l, num);
	IntListShow(l);

	if (!IntListOK(l)) {
		fprintf(stderr, "error: the list is not consistent - "
		                "please make sure that you have correctly "
		                "updated the fields of the IntList struct\n");
		IntListFree(l);
		exit(EXIT_FAILURE);
	}

	IntListFree(l);
}

static IntList readIntList(void) {
	char *line = NULL;
	size_t n = 0;
	if (getline(&line, &n, stdin) < 0) {
		fprintf(stderr, "failed to read list");
		free(line);
		exit(EXIT_FAILURE);
	}

	IntList l = IntListNew();
	char *start = line;
	char *token = strtok(line, " \t");
	while (token != NULL) {
		int num;
		if (sscanf(token, "%d", &num) == 1) {
			IntListAppend(l, num);
		} else {
			break;
		}
		token = strtok(NULL, " \t");
	}

	free(start);
	return l;
}

