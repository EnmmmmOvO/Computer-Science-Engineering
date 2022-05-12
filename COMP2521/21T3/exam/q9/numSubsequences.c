
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "list.h"

int isListBElement(int check, Node b);
int isCorrect(Node b, Node a, int mistake, int position);

// Worst case time complexity of this solution: O(...)
int numSubsequences(List listA, List listB, int tolerance) {
	int num = 0;
	int mistake = tolerance;
	Node a = listA->first;
	Node b = listB->first;
	for (; a != NULL; a = a->next) {
		int position = isListBElement(a->value, b);
		if (position < 0) continue;
		if (position + 1 > tolerance) continue;
		mistake -= position;
		if (isCorrect(b, a, mistake, position) < 0) continue;
		num++;
	}

	return num;
}

int isListBElement(int check, Node b) {
	for (int i = 0; b != NULL; i++, b = b->next) {
		if (check == b->value) return i;
	}
	return -1;
}

int isCorrect(Node b, Node a, int mistake, int position) {
	for (int i = 0; i <= position; i++) b = b->next;
	while (1) {
		if (a == NULL && b != NULL) {
			for (; b != NULL; b = b->next) {
				mistake--;
			}
			break;
		} else {
			break;
		}
		if (b->value != a->value) mistake--;
		b = b->next;
		a = a->next;
	}
	return mistake < 0 ? -1 : 0;
}