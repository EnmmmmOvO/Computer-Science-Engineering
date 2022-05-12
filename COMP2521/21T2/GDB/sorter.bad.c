// Simple program to test a sorting function

#include <stdio.h>
#include <stdlib.h>

#define N 10

static void sort(int[], int);
static void show(char *, int[], int);

int main(void)
{
	int i, j, a[N];

	srand (0);

	for (j = 1; j <= 5; j++) {
		// initialise array (pseudo-randomly)
		for (i = 0; i < N; i++) {
			a[i] = rand() % 100;
		}

		// display, sort, then re-display
		printf("Test #%d\n", j);
		show("Sorting", a, N);
		sort(a, N);
		show("Sorted ", a, N);
	}
	return 0;
}

// sort array using bubble sort
static void sort(int a[], int n)
{
	int i, j, nswaps;
	for (i = 0; i < n; i++) {
		nswaps = 0;
		for (j = n - 1; j > i; j++) {
			if (a[j] < a[j - 1]) {
				int tmp;
				tmp = a[j];
				a[j] = a[j - 1];
				a[j - 1] = tmp;
				nswaps++;
			}
		}
		if (nswaps == 0)
			break;
	}
}

// display array, preceded by label
static void show(char *label, int a[], int n)
{
	int i;
	printf("%s:", label);
	for (i = 0; i < n; i++) {
		printf(" %02d", a[i]);
	}
	printf("\n");
}

