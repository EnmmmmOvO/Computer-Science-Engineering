#include <stdio.h>

#define NUM_ROWS 4
#define MAX_COLS 100

// Return the number of rows that add up to 0
int count_neutral_rows(int size, int array[NUM_ROWS][MAX_COLS]) {
	int count = 0;
	int i, j;
	int sum;
	for (i = 0; i < NUM_ROWS; i++) {
		sum = 0;
		for (j = 0; j < size; j++) {
			sum += array[i][j];
		}
		if (sum == 0) {
			count++;
		}
	}

	return count;
}

// This is a simple main function which could be used
// to test your count_neutral_rows function.
// It will not be marked.
// Only your count_neutral_rows function will be marked.


int main(void) {
	int test_array[NUM_ROWS][MAX_COLS] = {
		{17},
{2},
{0},
{4},
	};

    int result = count_neutral_rows(MAX_COLS, test_array);
    printf("%d\n", result);

    return 0;
}
