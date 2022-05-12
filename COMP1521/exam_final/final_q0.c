// COMP1521 21T2 ... final exam, question 0

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int
count_leading_zeroes (uint32_t x)
{
	int number = 0;
	for (int loop = 31; loop >= 0; loop--) {
		if (x >> loop == 0) {
			number++;
		} else {
			break;
		}
	}
	return number;
}

