#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_LENGTH	(10001)

int main(void) {
	int num[MAX_LENGTH];
	int size = 0;

	while (scanf("%d", &num[size]) != EOF) {
		size++;
	}

	int i, j;
	int multiple = 0;
	for (i = 0; i < size; i++) {
		multiple = 0;

		for (j = 0; j < i; j++) {
			if (num[i] % num[j] == 0) {
				multiple = 1;
			}
		}

		if (multiple == 1) {
			printf("-1\n");
		} else {
			printf("%d\n", num[i]);
		}
	}
	
}
